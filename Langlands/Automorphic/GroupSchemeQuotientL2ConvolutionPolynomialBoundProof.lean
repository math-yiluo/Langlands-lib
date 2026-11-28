import Langlands.Automorphic.GroupSchemeQuotientL2ConvolutionPolynomialBoundStatement
import Langlands.Automorphic.GroupSchemeQuotientL2ContinuousRepresentativeProof
import Langlands.Global.AdelicRationalConjugateCountingAllPointsProof

/-! # Polynomial growth of continuous adelic convolution representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported ENNReal Pointwise

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme RepresentationGrowth

set_option maxHeartbeats 2000000 in
/-- Rational point counting and the positive subgroup Haar product give
polynomial bounds for the continuous representatives of quotient convolution. -/
theorem groupSchemeQuotientL2ConvolutionPolynomialBound :
    GroupSchemeQuotientL2ConvolutionPolynomialBoundStatement.{u} := by
  classical
  intro F _ _ G _ _ T i hi _ I _ e hc _ n ρ hn hρ
  dsimp only
  obtain ⟨d, hcount⟩ := adelicRationalConjugateCountingAllPoints F G n ρ hn hρ
  refine ⟨d, fun f hf => ?_⟩
  let Γ := rationalNormOneSubgroup F G
  let π₀ := positiveFactor F G T i hi I e
  let π₁ := normOneProjection F G T i hi I e hc
  let D := positiveRationalDecomposition F G T i hi I e hc
  let μ₀ := normalizedPositiveHaarMeasure F G T i hi I e hc
  let μ₁ : Measure Γ := Measure.count
  let μH := positiveRationalSubgroupHaarMeasure F G T i hi I e hc
  let S := tsupport f * (tsupport f)⁻¹
  have hS : IsCompact S := f.hasCompactSupport.mul f.hasCompactSupport.inv
  let C₀ := π₀ '' S
  have hC₀ : IsCompact C₀ := hS.image π₀.continuous
  let θ (y : AdelicGroupPoints F G) : AdelicGroupPoints F G := (π₁ y).val
  let C₁ := θ '' S
  have hC₁ : IsCompact C₁ := hS.image (continuous_subtype_val.comp π₁.continuous)
  have hpos (x s : AdelicGroupPoints F G) : π₀ (x * s * x⁻¹) = π₀ s := by
    simp only [map_mul, map_inv]
    rw [mul_comm (π₀ x) (π₀ s), mul_assoc, mul_inv_cancel, mul_one]
  have hconj (x s : AdelicGroupPoints F G) : θ (x * s * x⁻¹) = x * θ s * x⁻¹ := by
    change (positivePointMap F G T i (π₀ (x * s * x⁻¹)))⁻¹ * (x * s * x⁻¹) =
      x * ((positivePointMap F G T i (π₀ s))⁻¹ * s) * x⁻¹
    rw [hpos, ← mul_assoc, ← mul_assoc, (positivePointMap_commute F G T i hc (π₀ s) x).inv_left.eq]
    simp only [mul_assoc]
  obtain ⟨K, hK, hcard⟩ := hcount C₁ hC₁
  let : μ₀.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure F G T i hi I e hc
  have hμ₀ : μ₀ C₀ ≠ ∞ := hC₀.measure_lt_top.ne
  have hmass (x : AdelicGroupPoints F G) :
      μH.real (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S)) ≤
        (μ₀ C₀).toReal * K * adelicHeight F G ρ x ^ d := by
    let P := (rationalSubgroup F G : Set (AdelicGroupPoints F G)) ∩
      ((fun s => x * s * x⁻¹) '' C₁)
    let j (q : Γ) : AdelicGroupPoints F G := q.val.val
    have hj : Function.Injective j := fun _ _ h => Subtype.ext (Subtype.ext h)
    let Q := j ⁻¹' P
    obtain ⟨hP, hPb⟩ := hcard x
    have hQ : Q.Finite := hP.preimage hj.injOn
    have hQP : Q.ncard ≤ P.ncard := Set.ncard_le_ncard_of_injOn j
      (fun _ hq => hq) hj.injOn hP
    let U : Set (positiveRationalSubgroup F G T i) :=
      Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S)
    have hsub : D ⁻¹' U ⊆ C₀ ×ˢ Q := by
      rintro p ⟨s, hs, hp⟩
      have hp₀ : π₀ (D p).val = p.1 := positiveFactor_mul_normOne F G T i hi I e p.1 p.2.val
      have hp₁ : θ (D p).val = j p.2 :=
        congrArg (fun r : intrinsicSubgroup F T × Γ => r.2.val.val) (D.symm_apply_apply p)
      refine ⟨⟨s, hs, (hpos x s).symm.trans ((congrArg π₀ hp).trans hp₀)⟩, ?_⟩
      refine ⟨(rationalNormOneSubgroupInclusion F G p.2).property,
        θ s, mem_image_of_mem _ hs, ?_⟩
      exact (hconj x s).symm.trans ((congrArg θ hp).trans hp₁)
    have hpres : MeasurePreserving D.toHomeomorph.toMeasurableEquiv (μ₀.prod μ₁) μH :=
      measurePreserving_positiveRationalDecomposition F G T i hi I e hc
    have hcnt : μ₁ Q = Q.ncard := by
      rw [Set.ncard_eq_toFinset_card Q hQ]
      exact Measure.count_apply_finite Q hQ
    have hmul : μ₀ C₀ * μ₁ Q ≠ ∞ :=
      ENNReal.mul_ne_top hμ₀ (by rw [hcnt]; exact ENNReal.natCast_ne_top _)
    have hle : μH U ≤ μ₀ C₀ * μ₁ Q := by
      rw [← hpres.measure_preimage_equiv U, ← Measure.prod_prod]
      exact measure_mono hsub
    change (μH U).toReal ≤ _
    calc
      _ ≤ (μ₀ C₀ * μ₁ Q).toReal := ENNReal.toReal_mono hmul hle
      _ = (μ₀ C₀).toReal * (Q.ncard : ℝ) := by rw [ENNReal.toReal_mul, hcnt, ENNReal.toReal_natCast]
      _ ≤ (μ₀ C₀).toReal * (P.ncard : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hQP) ENNReal.toReal_nonneg
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hPb ENNReal.toReal_nonneg
  obtain ⟨M, hM⟩ := (f.hasCompactSupport.image f.continuous.norm).bddAbove
  let M₀ := max M 0
  have hM₀ (a : AdelicGroupPoints F G) : ‖f a‖ ≤ M₀ := by
    by_cases ha : a ∈ tsupport f
    · exact (hM (mem_image_of_mem _ ha)).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport ha, norm_zero]
      exact le_max_right _ _
  let A := M₀ * (∫ a, ‖f a‖ ∂(Measure.haar : Measure (AdelicGroupPoints F G))) *
    ((μ₀ C₀).toReal * K)
  have hA : 0 ≤ A := by
    refine mul_nonneg (mul_nonneg (le_max_right _ _) (integral_nonneg fun _ => norm_nonneg _))
      (mul_nonneg ENNReal.toReal_nonneg hK)
  refine ⟨Real.sqrt A, Real.sqrt_nonneg _, fun φ => ?_⟩
  obtain ⟨ψ, hψ, hrep, hbound⟩ :=
    groupSchemeQuotientL2ContinuousRepresentative F G T i hi I e hc f hf φ
  refine ⟨ψ, hψ, hrep, fun x => ?_⟩
  have hheight : 1 ≤ adelicHeight F G ρ x ^ d := one_le_pow₀ (one_le_adelicHeight F G ρ hn x)
  have hnorm := hbound x M₀ hM₀
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  calc
    _ ≤ M₀ * (∫ a, ‖f a‖ ∂(Measure.haar : Measure (AdelicGroupPoints F G))) *
        ((μ₀ C₀).toReal * K * adelicHeight F G ρ x ^ d) * ‖φ‖ ^ 2 := by
      refine hnorm.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
      exact mul_le_mul_of_nonneg_left (hmass x)
        (mul_nonneg (le_max_right _ _) (integral_nonneg fun _ => norm_nonneg _))
    _ = A * adelicHeight F G ρ x ^ d * ‖φ‖ ^ 2 := by
      dsimp only [A]
      rw [mul_assoc _ ((μ₀ C₀).toReal * K)]
    _ ≤ (Real.sqrt A * adelicHeight F G ρ x ^ d * ‖φ‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_self_pow₀ hheight (by decide)) hA)
        (sq_nonneg _)

end Langlands.Automorphic.GroupSchemeFunctions
