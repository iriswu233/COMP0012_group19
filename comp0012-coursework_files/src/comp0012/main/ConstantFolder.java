package comp0012.main;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.apache.bcel.Constants;
import org.apache.bcel.generic.DCONST;
import org.apache.bcel.generic.DSTORE;
import org.apache.bcel.generic.F2D;
import org.apache.bcel.generic.F2I;
import org.apache.bcel.generic.F2L;
import org.apache.bcel.generic.FCONST;
import org.apache.bcel.generic.FSTORE;
import org.apache.bcel.generic.I2D;
import org.apache.bcel.generic.I2F;
import org.apache.bcel.generic.I2L;
import org.apache.bcel.generic.ICONST;
import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.ISTORE;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionTargeter;
import org.apache.bcel.generic.L2D;
import org.apache.bcel.generic.L2F;
import org.apache.bcel.generic.L2I;
import org.apache.bcel.generic.LCONST;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.LSTORE;
import org.apache.bcel.generic.LoadInstruction;
import org.apache.bcel.generic.PUSH;
import org.apache.bcel.generic.SIPUSH;
import org.apache.bcel.generic.Select;
import org.apache.bcel.generic.StoreInstruction;
import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ALOAD;
import org.apache.bcel.generic.ASTORE;
import org.apache.bcel.generic.ArithmeticInstruction;
import org.apache.bcel.generic.BIPUSH;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ConversionInstruction;
import org.apache.bcel.generic.D2F;
import org.apache.bcel.generic.D2I;
import org.apache.bcel.generic.D2L;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.util.InstructionFinder;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.TargetLostException;

public class ConstantFolder {
	ClassParser parser = null;
	ClassGen gen = null;

	JavaClass original = null;
	JavaClass optimized = null;

	public ConstantFolder(String classFilePath) {
		try {
			this.parser = new ClassParser(classFilePath);
			this.original = this.parser.parse();
			this.gen = new ClassGen(this.original);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void optimize() {
		ClassGen cgen = new ClassGen(original);
		ConstantPoolGen cpgen = cgen.getConstantPool();
		cgen.setMajor(50);

		for (Method m : cgen.getMethods()) {
			if (m.isAbstract() || m.isNative() || m.getCode() == null)
				continue;

			MethodGen mg = new MethodGen(m, cgen.getClassName(), cpgen);
			InstructionList il = mg.getInstructionList();
			if (il == null)
				continue;

			boolean changed;
			int rounds = 0;

			do {
				changed = false;
				rounds++;

				// part1: simple folding
				changed |= foldNumericConversions(il, cpgen);
				changed |= foldNumeric(il, cpgen);

				// part2: constant variables across whole method
				changed |= propagateConstantVariables(il, cpgen);

				// part3: dynamic variables within intervals
				changed |= propagateDynamicVariables(il, cpgen);

				// part4: extra peephole
				changed |= removeOverwrittenStores(il, cpgen);
				changed |= removeDeadStores(il, cpgen);

				if (rounds > 50)
					break;
			} while (changed);

			mg.removeNOPs();
			mg.removeLocalVariables();
			mg.removeLineNumbers();
			mg.removeCodeAttributes();
			mg.setMaxStack();
			mg.setMaxLocals();

			cgen.replaceMethod(m, mg.getMethod());
		}

		this.optimized = cgen.getJavaClass();
	}

	// Part1
	private boolean foldNumericConversions(InstructionList il, ConstantPoolGen cpgen) {
		boolean changed = false;

		boolean onceChanged;
		do {
			onceChanged = false;

			for (InstructionHandle h1 = il.getStart(); h1 != null; h1 = h1.getNext()) {
				InstructionHandle h2 = h1.getNext();
				if (h2 == null)
					break;

				Instruction conv = h2.getInstruction();
				if (!(conv instanceof ConversionInstruction))
					continue;

				if (conv instanceof I2L) {
					Integer v = getPushedIntConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (long) v.intValue())) {
						onceChanged = changed = true;
						break;
					}
				} else if (conv instanceof I2F) {
					Integer v = getPushedIntConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (float) v.intValue())) {
						onceChanged = changed = true;
						break;
					}
				} else if (conv instanceof I2D) {
					Integer v = getPushedIntConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (double) v.intValue())) {
						onceChanged = changed = true;
						break;
					}
				}

				else if (conv instanceof L2I) {
					Long v = getPushedLongConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (int) v.longValue())) {
						onceChanged = changed = true;
						break;
					}
				} else if (conv instanceof L2F) {
					Long v = getPushedLongConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (float) v.longValue())) {
						onceChanged = changed = true;
						break;
					}
				} else if (conv instanceof L2D) {
					Long v = getPushedLongConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (double) v.longValue())) {
						onceChanged = changed = true;
						break;
					}
				}

				else if (conv instanceof F2I) {
					Float v = getPushedFloatConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (int) v.floatValue())) {
						onceChanged = changed = true;
						break;
					}
				} else if (conv instanceof F2L) {
					Float v = getPushedFloatConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (long) v.floatValue())) {
						onceChanged = changed = true;
						break;
					}
				} else if (conv instanceof F2D) {
					Float v = getPushedFloatConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (double) v.floatValue())) {
						onceChanged = changed = true;
						break;
					}
				}

				else if (conv instanceof D2I) {
					Double v = getPushedDoubleConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (int) v.doubleValue())) {
						onceChanged = changed = true;
						break;
					}
				} else if (conv instanceof D2L) {
					Double v = getPushedDoubleConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (long) v.doubleValue())) {
						onceChanged = changed = true;
						break;
					}
				} else if (conv instanceof D2F) {
					Double v = getPushedDoubleConstant(h1, cpgen);
					if (v != null && replace2WithPush(il, cpgen, h1, h2, (float) v.doubleValue())) {
						onceChanged = changed = true;
						break;
					}
				}
			}
		} while (onceChanged);

		return changed;
	}

	private boolean foldNumeric(InstructionList il, ConstantPoolGen cpgen) {
		boolean changed = false;

		boolean onceChanged;
		do {
			onceChanged = false;

			for (InstructionHandle h1 = il.getStart(); h1 != null; h1 = h1.getNext()) {
				InstructionHandle h2 = h1.getNext();
				if (h2 == null)
					break;
				InstructionHandle h3 = h2.getNext();
				if (h3 == null)
					break;

				Instruction op = h3.getInstruction();
				if (!(op instanceof ArithmeticInstruction))
					continue;

				Integer i1 = getPushedIntConstant(h1, cpgen);
				Integer i2 = getPushedIntConstant(h2, cpgen);
				if (i1 != null && i2 != null) {
					Integer r = evalIntBinary(i1, i2, op);
					if (r != null) {
						if (replace3WithPush(il, cpgen, h1, h2, h3, r)) {
							onceChanged = changed = true;
							break;
						}
					}
					continue;
				}

				Long l1 = getPushedLongConstant(h1, cpgen);
				Long l2 = getPushedLongConstant(h2, cpgen);
				if (l1 != null && l2 != null) {
					Long r = evalLongBinary(l1, l2, op);
					if (r != null) {
						if (replace3WithPush(il, cpgen, h1, h2, h3, r)) {
							onceChanged = changed = true;
							break;
						}
					}
					continue;
				}

				Float f1 = getPushedFloatConstant(h1, cpgen);
				Float f2 = getPushedFloatConstant(h2, cpgen);
				if (f1 != null && f2 != null) {
					Float r = evalFloatBinary(f1, f2, op);
					if (r != null) {
						if (replace3WithPush(il, cpgen, h1, h2, h3, r)) {
							onceChanged = changed = true;
							break;
						}
					}
					continue;
				}

				Double d1 = getPushedDoubleConstant(h1, cpgen);
				Double d2 = getPushedDoubleConstant(h2, cpgen);
				if (d1 != null && d2 != null) {
					Double r = evalDoubleBinary(d1, d2, op);
					if (r != null) {
						if (replace3WithPush(il, cpgen, h1, h2, h3, r)) {
							onceChanged = changed = true;
							break;
						}
					}
				}
			}
		} while (onceChanged);

		return changed;
	}

	private boolean replace2WithPush(InstructionList il, ConstantPoolGen cpgen,
			InstructionHandle h1, InstructionHandle h2,
			Number value) {
		try {
			h1.setInstruction(new PUSH(cpgen, value).getInstruction());
			il.delete(h2);
			return true;
		} catch (TargetLostException e) {
			retargetLostTargets(e, h1);
			return true;
		}
	}

	private boolean replace3WithPush(InstructionList il, ConstantPoolGen cpgen,
			InstructionHandle h1, InstructionHandle h2, InstructionHandle h3,
			Number value) {
		try {
			h1.setInstruction(new PUSH(cpgen, value).getInstruction());
			il.delete(h2, h3);
			return true;
		} catch (TargetLostException e) {
			retargetLostTargets(e, h1);
			return true;
		}
	}

	private void retargetLostTargets(TargetLostException e, InstructionHandle newTarget) {
		InstructionHandle[] lost = e.getTargets();
		for (InstructionHandle t : lost) {
			InstructionTargeter[] targeters = t.getTargeters();
			if (targeters == null)
				continue;
			for (InstructionTargeter it : targeters) {
				it.updateTarget(t, newTarget);
			}
		}
	}

	private Integer getPushedIntConstant(InstructionHandle h, ConstantPoolGen cpgen) {
		Instruction inst = h.getInstruction();
		if (inst instanceof ICONST)
			return ((ICONST) inst).getValue().intValue();
		if (inst instanceof BIPUSH)
			return ((BIPUSH) inst).getValue().intValue();
		if (inst instanceof SIPUSH)
			return ((SIPUSH) inst).getValue().intValue();
		if (inst instanceof LDC) {
			Object v = ((LDC) inst).getValue(cpgen);
			return (v instanceof Integer) ? (Integer) v : null;
		}
		return null;
	}

	private Integer evalIntBinary(int a, int b, Instruction op) {
		switch (op.getOpcode()) {
			case Constants.IADD:
				return a + b;
			case Constants.ISUB:
				return a - b;
			case Constants.IMUL:
				return a * b;
			case Constants.IDIV:
				if (b == 0)
					return null;
				return a / b;
			case Constants.IREM:
				if (b == 0)
					return null;
				return a % b;
			default:
				return null;
		}
	}

	private Long getPushedLongConstant(InstructionHandle h, ConstantPoolGen cpgen) {
		Instruction inst = h.getInstruction();
		if (inst instanceof LCONST)
			return ((LCONST) inst).getValue().longValue();
		if (inst instanceof LDC2_W) {
			Object v = ((LDC2_W) inst).getValue(cpgen);
			return (v instanceof Long) ? (Long) v : null;
		}
		return null;
	}

	private Long evalLongBinary(long a, long b, Instruction op) {
		switch (op.getOpcode()) {
			case Constants.LADD:
				return a + b;
			case Constants.LSUB:
				return a - b;
			case Constants.LMUL:
				return a * b;
			case Constants.LDIV:
				if (b == 0L)
					return null;
				return a / b;
			case Constants.LREM:
				if (b == 0L)
					return null;
				return a % b;
			default:
				return null;
		}
	}

	private Float getPushedFloatConstant(InstructionHandle h, ConstantPoolGen cpgen) {
		Instruction inst = h.getInstruction();
		if (inst instanceof FCONST)
			return ((FCONST) inst).getValue().floatValue();
		if (inst instanceof LDC) {
			Object v = ((LDC) inst).getValue(cpgen);
			return (v instanceof Float) ? (Float) v : null;
		}
		return null;
	}

	private Float evalFloatBinary(float a, float b, Instruction op) {
		switch (op.getOpcode()) {
			case Constants.FADD:
				return a + b;
			case Constants.FSUB:
				return a - b;
			case Constants.FMUL:
				return a * b;
			case Constants.FDIV:
				return a / b;
			case Constants.FREM:
				return a % b;
			default:
				return null;
		}
	}

	private Double getPushedDoubleConstant(InstructionHandle h, ConstantPoolGen cpgen) {
		Instruction inst = h.getInstruction();
		if (inst instanceof DCONST)
			return ((DCONST) inst).getValue().doubleValue();
		if (inst instanceof LDC2_W) {
			Object v = ((LDC2_W) inst).getValue(cpgen);
			return (v instanceof Double) ? (Double) v : null;
		}
		return null;
	}

	private Double evalDoubleBinary(double a, double b, Instruction op) {
		switch (op.getOpcode()) {
			case Constants.DADD:
				return a + b;
			case Constants.DSUB:
				return a - b;
			case Constants.DMUL:
				return a * b;
			case Constants.DDIV:
				return a / b;
			case Constants.DREM:
				return a % b;
			default:
				return null;
		}
	}

	// part2
	private boolean propagateConstantVariables(InstructionList il, ConstantPoolGen cpgen) {
		boolean changed = false;

		HashMap<Integer, Integer> storeCount = new HashMap<>();
		HashMap<Integer, Number> constantVars = new HashMap<>();

		for (InstructionHandle h = il.getStart(); h != null; h = h.getNext()) {
			Instruction inst = h.getInstruction();

			if (inst instanceof StoreInstruction && !(inst instanceof ASTORE)) {
				int index = ((StoreInstruction) inst).getIndex();
				int count = storeCount.getOrDefault(index, 0) + 1;
				storeCount.put(index, count);

				InstructionHandle prev = h.getPrev();
				if (prev != null) {
					Number val = getTypedConstant(prev, inst, cpgen);
					if (val != null) {
						constantVars.put(index, val);
					} else {
						constantVars.remove(index);
					}
				} else {
					constantVars.remove(index);
				}
			}

			if (inst instanceof IINC) {
				int index = ((IINC) inst).getIndex();
				storeCount.put(index, storeCount.getOrDefault(index, 0) + 1);
				constantVars.remove(index);
			}
		}

		Iterator<Map.Entry<Integer, Number>> it = constantVars.entrySet().iterator();
		while (it.hasNext()) {
			Map.Entry<Integer, Number> entry = it.next();
			if (storeCount.getOrDefault(entry.getKey(), 0) != 1) {
				it.remove();
			}
		}
		if (constantVars.isEmpty())
			return false;

		for (InstructionHandle h = il.getStart(); h != null; h = h.getNext()) {
			Instruction inst = h.getInstruction();

			if (inst instanceof LoadInstruction && !(inst instanceof ALOAD)) {
				int index = ((LoadInstruction) inst).getIndex();
				if (constantVars.containsKey(index)) {
					Number value = constantVars.get(index);
					Instruction push = createTypedPush(cpgen, value);
					if (push != null) {
						h.setInstruction(push);
						changed = true;
					}
				}
			}
		}
		return changed;
	}

	private Number getTypedConstant(InstructionHandle h, Instruction storeInst, ConstantPoolGen cpgen) {
		if (storeInst instanceof ISTORE)
			return getPushedIntConstant(h, cpgen);
		if (storeInst instanceof LSTORE)
			return getPushedLongConstant(h, cpgen);
		if (storeInst instanceof FSTORE)
			return getPushedFloatConstant(h, cpgen);
		if (storeInst instanceof DSTORE)
			return getPushedDoubleConstant(h, cpgen);
		return null;
	}

	private Instruction createTypedPush(ConstantPoolGen cpgen, Number value) {
		if (value instanceof Integer)
			return new PUSH(cpgen, value.intValue()).getInstruction();
		if (value instanceof Long)
			return new PUSH(cpgen, value.longValue()).getInstruction();
		if (value instanceof Float)
			return new PUSH(cpgen, value.floatValue()).getInstruction();
		if (value instanceof Double)
			return new PUSH(cpgen, value.doubleValue()).getInstruction();
		return null;
	}

	// part3
	private boolean propagateDynamicVariables(InstructionList il, ConstantPoolGen cpgen) {
		Map<Integer, Number> constantVars = new HashMap<>();
		HashMap<Integer, Boolean> iincVars = new HashMap<>();
		boolean changed = false;

		for (InstructionHandle h = il.getStart(); h != null; h = h.getNext()) {
			if (h.getInstruction() instanceof IINC) {
				iincVars.put(((IINC) h.getInstruction()).getIndex(), true);
			}
		}

		for (InstructionHandle h = il.getStart(); h != null; h = h.getNext()) {
			Instruction inst = h.getInstruction();

			if (inst instanceof StoreInstruction && !(inst instanceof ASTORE)) {
				int index = ((StoreInstruction) inst).getIndex();

				if (iincVars.containsKey(index)) {
					continue;
				}

				InstructionHandle prev = h.getPrev();
				if (prev != null) {
					Number val = getTypedConstant(prev, inst, cpgen);
					if (val != null) {
						constantVars.put(index, val);
					} else {
						constantVars.remove(index);
					}
				} else {
					constantVars.remove(index);
				}
			} else if (inst instanceof LoadInstruction && !(inst instanceof ALOAD)) {
				int index = ((LoadInstruction) inst).getIndex();
				if (constantVars.containsKey(index)) {
					Number value = constantVars.get(index);
					Instruction push = createTypedPush(cpgen, value);
					if (push != null) {
						h.setInstruction(push);
						changed = true;
					}
				}
			} else if (inst instanceof IINC) {
				int index = ((IINC) inst).getIndex();
				constantVars.remove(index);
			} else if (inst instanceof ArithmeticInstruction) {

				InstructionHandle prev1 = h.getPrev();
				InstructionHandle prev2 = (prev1 != null) ? prev1.getPrev() : null;

				if (prev1 != null && prev2 != null) {
					Number v1 = getTypedConstant(prev1, prev1.getInstruction(), cpgen);
					Number v2 = getTypedConstant(prev2, prev2.getInstruction(), cpgen);
					if (v1 != null && v2 != null) {

						Number result = null;
						if (v1 instanceof Integer && v2 instanceof Integer)
							result = evalIntBinary(v1.intValue(), v2.intValue(), inst);
						else if (v1 instanceof Long && v2 instanceof Long)
							result = evalLongBinary(v1.longValue(), v2.longValue(), inst);
						else if (v1 instanceof Float && v2 instanceof Float)
							result = evalFloatBinary(v1.floatValue(), v2.floatValue(), inst);
						else if (v1 instanceof Double && v2 instanceof Double)
							result = evalDoubleBinary(v1.doubleValue(), v2.doubleValue(), inst);

						if (result != null) {
							Instruction push = createTypedPush(cpgen, result);
							if (push != null) {
								h.setInstruction(push);

								try {
									il.delete(prev2, prev1);
								} catch (TargetLostException e) {
									for (InstructionHandle target : e.getTargets()) {
										for (InstructionTargeter targeter : target.getTargeters()) {
											targeter.updateTarget(target, h);
										}
									}
								}

								changed = true;
								break;
							}
						}
					}
				}
			}
		}

		return changed;
	}

	// part4
	private boolean removeOverwrittenStores(InstructionList il, ConstantPoolGen cpgen) {
		boolean changed = false;

		for (InstructionHandle h = il.getStart(); h != null;) {
			InstructionHandle cur = h;
			h = h.getNext();

			Instruction inst = cur.getInstruction();
			if (!(inst instanceof StoreInstruction) || (inst instanceof ASTORE))
				continue;
			if (isBranchTarget(cur))
				continue;

			int idx = ((StoreInstruction) inst).getIndex();
			InstructionHandle scan = cur.getNext();
			boolean overwritten = false;

			while (scan != null) {
				Instruction scanInstruction = scan.getInstruction();
				if (isBranchTarget(scan))
					break;
				if (scanInstruction instanceof BranchInstruction || scanInstruction instanceof Select)
					break;
				if (scanInstruction instanceof LoadInstruction && !(scanInstruction instanceof ALOAD)
						&& ((LoadInstruction) scanInstruction).getIndex() == idx) {
					overwritten = false;
					break;
				}

				if (scanInstruction instanceof StoreInstruction && !(scanInstruction instanceof ASTORE)
						&& ((StoreInstruction) scanInstruction).getIndex() == idx) {
					overwritten = true;
					break;
				}

				if (scanInstruction instanceof IINC && ((IINC) scanInstruction).getIndex() == idx) {
					overwritten = true;
					break;
				}

				scan = scan.getNext();
			}

			if (!overwritten)
				continue;

			InstructionHandle prev = cur.getPrev();
			if (prev == null)
				continue;
			if (isBranchTarget(prev))
				continue;
			if (!isSinglePushConstant(prev.getInstruction(), cpgen))
				continue;

			try {
				il.delete(prev, cur);
				changed = true;
			} catch (TargetLostException e) {
				InstructionHandle newTarget = (cur.getNext() != null) ? cur.getNext() : prev.getPrev();
				if (newTarget != null)
					retargetLostTargets(e, newTarget);
				changed = true;
			}
		}
		return changed;
	}

	private boolean removeDeadStores(InstructionList il, ConstantPoolGen cpgen) {
		boolean changed = false;

		java.util.HashMap<Integer, Integer> loads = new java.util.HashMap<>();
		for (InstructionHandle h = il.getStart(); h != null; h = h.getNext()) {
			Instruction inst = h.getInstruction();

			if (inst instanceof LoadInstruction && !(inst instanceof ALOAD)) {
				int idx = ((LoadInstruction) inst).getIndex();
				loads.put(idx, loads.getOrDefault(idx, 0) + 1);
			} else if (inst instanceof IINC) {
				int idx = ((IINC) inst).getIndex();
				loads.put(idx, loads.getOrDefault(idx, 0) + 1);
			}
		}

		for (InstructionHandle h = il.getStart(); h != null;) {
			InstructionHandle cur = h;
			h = h.getNext(); // advance before delete

			Instruction inst = cur.getInstruction();
			if (!(inst instanceof StoreInstruction) || (inst instanceof ASTORE))
				continue;

			int idx = ((StoreInstruction) inst).getIndex();

			// Only remove stores to locals that are never read
			if (loads.getOrDefault(idx, 0) != 0)
				continue;

			// Don't delete branch targets
			if (isBranchTarget(cur))
				continue;

			InstructionHandle prev = cur.getPrev();
			if (prev == null)
				continue;
			if (isBranchTarget(prev))
				continue;

			if (!isSinglePushConstant(prev.getInstruction(), cpgen))
				continue;

			try {
				il.delete(prev, cur);
				changed = true;
			} catch (TargetLostException e) {
				InstructionHandle newTarget = (cur.getNext() != null) ? cur.getNext() : prev.getPrev();
				if (newTarget != null)
					retargetLostTargets(e, newTarget);
				changed = true;
			}
		}

		return changed;
	}

	private boolean isBranchTarget(InstructionHandle h) {
		InstructionTargeter[] targeters = h.getTargeters();
		if (targeters == null)
			return false;

		for (InstructionTargeter t : targeters) {
			if (t instanceof BranchInstruction)
				return true;
			if (t instanceof Select)
				return true; // switch targets
		}
		return false;
	}

	private boolean isSinglePushConstant(Instruction inst, ConstantPoolGen cpgen) {
		if (inst instanceof ICONST)
			return true;
		if (inst instanceof BIPUSH)
			return true;
		if (inst instanceof SIPUSH)
			return true;
		if (inst instanceof LCONST)
			return true;
		if (inst instanceof FCONST)
			return true;
		if (inst instanceof DCONST)
			return true;

		if (inst instanceof LDC) {
			Object v = ((LDC) inst).getValue(cpgen);
			return (v instanceof Integer) || (v instanceof Float);
		}
		if (inst instanceof LDC2_W) {
			Object v = ((LDC2_W) inst).getValue(cpgen);
			return (v instanceof Long) || (v instanceof Double);
		}
		return false;
	}

	public void write(String optimisedFilePath) {
		this.optimize();

		try {
			FileOutputStream out = new FileOutputStream(new File(optimisedFilePath));
			this.optimized.dump(out);
		} catch (FileNotFoundException e) {

			e.printStackTrace();
		} catch (IOException e) {

			e.printStackTrace();
		}
	}
}