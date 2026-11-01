import Langlands.Geometry.Analytic.ValuedField.SeminormRealizationStatement
import Mathlib.RingTheory.Valuation.Quotient
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion

/-! # Realization through the quotient, fraction field and completion -/

noncomputable section

universe u

namespace Langlands.Analytic

open scoped NNReal

/-- Every ultrametric multiplicative seminorm is realized in a complete
ultrametric normed field in the universe of its source ring. -/
theorem seminormRealization : SeminormRealizationStatement.{u} := by
  intro A _ q hq
  let v : Valuation A ℝ≥0 := {
    toFun := fun a => ⟨q a, apply_nonneg q a⟩
    map_zero' := Subtype.ext (map_zero q)
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun a b => Subtype.ext (map_mul q a b)
    map_add_le_max' := hq
  }
  let D := A ⧸ v.supp
  let : CommRing D := inferInstanceAs (CommRing (A ⧸ v.supp))
  let : IsDomain D := inferInstanceAs (IsDomain (A ⧸ v.supp))
  let dv : Valuation D ℝ≥0 := v.onQuot le_rfl
  have hdv (a : D) : dv a = 0 ↔ a = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := v.supp) a
    change v a = 0 ↔ (Ideal.Quotient.mk v.supp a : A ⧸ v.supp) = 0
    exact (Ideal.Quotient.eq_zero_iff_mem (I := v.supp) (a := a)).symm
  let R := FractionRing D
  have hdenom : nonZeroDivisors D ≤ dv.supp.primeCompl :=
    fun a ha hz => (nonZeroDivisors.ne_zero ha) ((hdv a).mp hz)
  let w : Valuation R ℝ≥0 := dv.extendToLocalization hdenom R
  let abv : AbsoluteValue R ℝ := {
    toFun := fun a => w a
    map_mul' := fun a b => congrArg NNReal.toReal (map_mul w a b)
    nonneg' := fun _ => NNReal.coe_nonneg _
    eq_zero' := fun _ => NNReal.coe_eq_zero.trans (Valuation.zero_iff _)
    add_le' := fun a b =>
      (show (w (a + b) : ℝ) ≤ max (w a : ℝ) (w b : ℝ) from
        w.map_add a b).trans
        (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
  }
  let N := WithAbs abv
  let : IsUltrametricDist N :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (fun a b => w.map_add a.ofAbs b.ofAbs)
  let f : A →+* N :=
    (WithAbs.equiv abv).symm.toRingHom.comp
      ((algebraMap D R).comp (Ideal.Quotient.mk v.supp))
  have hnorm (a : A) : ‖f a‖ = q a :=
    congrArg NNReal.toReal
      (dv.extendToLocalization_apply_map_apply hdenom R
        (Ideal.Quotient.mk v.supp a))
  let L := UniformSpace.Completion N
  let : IsUltrametricDist L := by
    apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    intro a b
    induction a, b using UniformSpace.Completion.induction_on₂ with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a b =>
        change ‖(a : UniformSpace.Completion N) + (b : UniformSpace.Completion N)‖ ≤
          max ‖(a : UniformSpace.Completion N)‖ ‖(b : UniformSpace.Completion N)‖
        rw [← UniformSpace.Completion.coe_add]
        simpa only [UniformSpace.Completion.norm_coe] using
          IsUltrametricDist.norm_add_le_max a b
  refine ⟨L, inferInstance, inferInstance, inferInstance,
    UniformSpace.Completion.coeRingHom.comp f, ?_⟩
  intro a
  change ‖(f a : UniformSpace.Completion N)‖ = q a
  rw [UniformSpace.Completion.norm_coe, hnorm]

end Langlands.Analytic
