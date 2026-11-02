import Langlands.LocalField.ResidueNormalization
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Local-field units for Plancherel character evaluation

Only units and sign adapters of the published unrestricted field API are
constructed here. The field, valuation, order, residue field and absolute
value remain the published objects.
-/

noncomputable section

open scoped NNReal WithZero

namespace Langlands.Plancherel

universe uF

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem field_residue_nnreal_gt_one :
    (1 : ℝ≥0) < (LocalField.residueCardinality F : ℝ≥0) := by
  exact_mod_cast LocalField.residueCardinality_gt_one F

/-- Restriction of the actual residue-normalized absolute value to field
units, with values bundled as positive units. -/
def fieldNormUnits : Fˣ →* ℝ≥0ˣ :=
  Units.map (((WithZeroMulInt.toNNReal (field_residue_nnreal_gt_one F).ne_zero).comp
    (FML.normalizedMultiplicativeValuation F).toMonoidWithZeroHom).toMonoidHom)

@[simp]
theorem fieldNormUnits_val (a : Fˣ) :
    ((fieldNormUnits F a : ℝ≥0) : ℝ) =
      LocalField.residueNormalizedAbsoluteValue F (a : F) := rfl

/-- The existing units valuation with its sign converted to the source's
positive additive order. -/
def fieldOrderUnits : Fˣ →* Multiplicative ℤ :=
  (NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationUnitsMulHom F)⁻¹

theorem fieldOrderUnits_toAdd (a : Fˣ) :
    (fieldOrderUnits F a).toAdd =
      -WithZero.log (FML.normalizedMultiplicativeValuation F (a : F)) := by
  change -((NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationUnitsMulHom F a).toAdd) = _
  exact congrArg Neg.neg (WithZero.logEquiv_apply _)

/-- This is exactly the published additive order on nonzero elements. -/
theorem fieldOrderUnits_ord (a : Fˣ) :
    FML.ord F (a : F) = ((fieldOrderUnits F a).toAdd : WithTop ℤ) := by
  rw [FML.ord_of_ne_zero F a.ne_zero, fieldOrderUnits_toAdd]

/-- The actual residue-cardinality normalization on field units. -/
theorem fieldNormUnits_zpow (a : Fˣ) :
    ((fieldNormUnits F a : ℝ≥0) : ℝ) =
      (LocalField.residueCardinality F : ℝ) ^ (-(fieldOrderUnits F a).toAdd) :=
  LocalField.residueNormalizedAbsoluteValue_of_ord_eq F (fieldOrderUnits_ord F a)

/-- The same normalization using real exponentiation and Waldspurger's sign. -/
theorem fieldNormUnits_rpow (a : Fˣ) :
    (LocalField.residueCardinality F : ℝ) ^ (-((fieldOrderUnits F a).toAdd : ℝ)) =
      ((fieldNormUnits F a : ℝ≥0) : ℝ) := by
  rw [fieldNormUnits_zpow, ← Int.cast_neg, Real.rpow_intCast]

/-- The two actual field-unit maps have exactly the same unit kernel. -/
theorem fieldNormUnits_eq_one_iff (a : Fˣ) :
    fieldNormUnits F a = 1 ↔ fieldOrderUnits F a = 1 := by
  have hq : (LocalField.residueCardinality F : ℝ) ≠ 1 := by
    exact_mod_cast (LocalField.residueCardinality_gt_one F).ne'
  change fieldNormUnits F a = 1 ↔ (fieldOrderUnits F a).toAdd = 0
  constructor
  · intro h
    have hr := congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) h
    rw [fieldNormUnits_zpow] at hr
    exact neg_eq_zero.mp ((zpow_eq_one_iff_right₀ (Nat.cast_nonneg _) hq).mp hr)
  · intro h
    apply Units.ext
    apply NNReal.eq
    change ((fieldNormUnits F a : ℝ≥0) : ℝ) = 1
    rw [fieldNormUnits_zpow, h]
    simp

/-- The kernel is the already defined integral-unit subgroup. -/
theorem fieldOrderUnits_ker : (fieldOrderUnits F).ker = FML.unitGroup F := by
  ext a
  rw [FML.mem_unitGroup_iff_ord_eq_zero, fieldOrderUnits_ord]
  change (fieldOrderUnits F a).toAdd = 0 ↔
    ((fieldOrderUnits F a).toAdd : WithTop ℤ) = 0
  simp

theorem fieldNormUnits_ker : (fieldNormUnits F).ker = FML.unitGroup F := by
  rw [← fieldOrderUnits_ker F]
  ext a
  exact fieldNormUnits_eq_one_iff F a

/-- Every integer order occurs on actual field units. -/
theorem fieldOrderUnits_surjective : Function.Surjective (fieldOrderUnits F) := by
  intro n
  obtain ⟨x, hx, hn⟩ := FML.ord_surjective_nonzero F n.toAdd
  refine ⟨Units.mk0 x hx, ?_⟩
  change (fieldOrderUnits F (Units.mk0 x hx)).toAdd = n.toAdd
  apply WithTop.coe_injective
  rw [← fieldOrderUnits_ord]
  exact hn

end Langlands.Plancherel
