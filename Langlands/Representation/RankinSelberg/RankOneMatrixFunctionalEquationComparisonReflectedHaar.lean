import Langlands.Representation.Whittaker.DualTransform
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentIota
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.MeasureTheory.Integral.Prod

/-! Haar transport for the actual Weyl-reflected inverse-transpose unipotent. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory MeasureTheory.Measure GeneralLinear Whittaker
open scoped NNReal

universe uG uK uA

/-- An involutive continuous group automorphism preserves every regular Haar
measure. Its positive Haar modulus has square one. -/
theorem measurePreserving_involutive_automorphism
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ* G) (he : Function.Involutive e)
    (μ : Measure G) [IsHaarMeasure μ] [Regular μ] :
    MeasurePreserving e μ μ := by
  have hee : e.trans e = ContinuousMulEquiv.refl G := by
    ext g
    exact he g
  have hsq : mulEquivHaarChar e * mulEquivHaarChar e = 1 := by
    rw [← mulEquivHaarChar_trans, hee, mulEquivHaarChar_refl]
  have hc : mulEquivHaarChar e = 1 := by
    apply NNReal.coe_injective
    apply (pow_eq_one_iff_of_nonneg (NNReal.coe_nonneg _) (by decide : 2 ≠ 0)).mp
    simpa only [pow_two, NNReal.coe_mul, NNReal.coe_one] using
      congrArg (fun c : ℝ≥0 => (c : ℝ)) hsq
  refine ⟨e.continuous.measurable, ?_⟩
  simpa only [hc, one_smul] using mulEquivHaarChar_smul_map μ e

section Reflected

variable {K : Type uK} [CommRing K] (n : ℕ)

/-- The published reflected unipotent is an involution on the actual group. -/
theorem reflectedUnipotent_involutive :
    Function.Involutive (reflectedUnipotent (F := K) (n := n)) := by
  intro u
  apply Subtype.ext
  simp only [reflectedUnipotent_val, map_mul, inverseTranspose_weylLong,
    inverseTranspose_involutive, mul_assoc, weylLong_mul_self, mul_one]
  rw [← mul_assoc, weylLong_mul_self, one_mul]

/-- Reflection changes the inverse-transpose Weyl factor to ordinary left
multiplication, in the unsigned convention. -/
theorem inverseTranspose_reflected_mul_weyl (u : upperUnipotent (n + 1) K) :
    inverseTranspose (n + 1) K (reflectedUnipotent u).val * weylLong (n + 1) K =
      weylLong (n + 1) K * u.val := by
  simp only [reflectedUnipotent_val, map_mul, inverseTranspose_weylLong,
    inverseTranspose_involutive, mul_assoc, weylLong_mul_self, mul_one]

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- Weyl-reflected inverse transpose as a continuous automorphism of the actual
upper-unipotent group. -/
def reflectedUnipotentEquiv :
    upperUnipotent (n + 1) K ≃ₜ* upperUnipotent (n + 1) K where
  toFun := reflectedUnipotent
  invFun := reflectedUnipotent
  left_inv := reflectedUnipotent_involutive n
  right_inv := reflectedUnipotent_involutive n
  map_mul' u v := by
    apply Subtype.ext
    simp only [reflectedUnipotent_val, Subgroup.coe_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (weylLong (n + 1) K) (weylLong (n + 1) K),
      weylLong_mul_self, one_mul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul
      ((continuous_inverseTranspose (n + 1) K).comp continuous_subtype_val)).mul
        continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul
      ((continuous_inverseTranspose (n + 1) K).comp continuous_subtype_val)).mul
        continuous_const

@[simp] theorem reflectedUnipotentEquiv_apply (u : upperUnipotent (n + 1) K) :
    reflectedUnipotentEquiv n u = reflectedUnipotent u := rfl

variable [MeasurableSpace (upperUnipotent (n + 1) K)]
  [BorelSpace (upperUnipotent (n + 1) K)]
  [LocallyCompactSpace (upperUnipotent (n + 1) K)]

/-- The reflection contributes no Haar scalar, independently of normalization. -/
theorem measurePreserving_reflectedUnipotent
    (μ : Measure (upperUnipotent (n + 1) K)) [IsHaarMeasure μ] [Regular μ] :
    MeasurePreserving (reflectedUnipotent (F := K) (n := n)) μ μ :=
  measurePreserving_involutive_automorphism (reflectedUnipotentEquiv n)
    (reflectedUnipotent_involutive n) μ

/-- The same reflection preserves the full product measure, with the second
variable unchanged. -/
theorem measurePreserving_reflectedUnipotent_prod
    (μ : Measure (upperUnipotent (n + 1) K)) [IsHaarMeasure μ] [Regular μ]
    [SFinite μ] {A : Type uA} [MeasurableSpace A] (ν : Measure A) [SFinite ν] :
    MeasurePreserving
      (fun z : upperUnipotent (n + 1) K × A => (reflectedUnipotent z.1, z.2))
      (μ.prod ν) (μ.prod ν) :=
  (measurePreserving_reflectedUnipotent n μ).prod (MeasurePreserving.id ν)

end Reflected

/-- In particular, reflection preserves the actual integral-subgroup-normalized
unipotent Haar measure over every nonarchimedean local field. -/
theorem measurePreserving_reflectedUnipotent_unipotentHaar
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ)
    [MeasurableSpace (upperUnipotent (n + 1) K)]
    [BorelSpace (upperUnipotent (n + 1) K)] :
    MeasurePreserving (reflectedUnipotent (F := K) (n := n))
      (unipotentHaar K n) (unipotentHaar K n) := by
  have := localField_t2 K
  have : LocallyCompactSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin (n + 1) → Fin (n + 1) → K))
  have : LocallyCompactSpace (upperUnipotent (n + 1) K) :=
    UpperUnipotent.locallyCompactSpace
  exact measurePreserving_reflectedUnipotent n (unipotentHaar K n)

end Langlands.RankinSelberg
