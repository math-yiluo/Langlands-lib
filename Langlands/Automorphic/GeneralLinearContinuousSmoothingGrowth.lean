import Langlands.Automorphic.GroupSchemeQuotientL2ContinuousRepresentativeStatement
import Langlands.Global.AdelicGLPositiveRationalConjugateGrowth

/-! # Slice-wise moderate growth of positive-quotient smoothing on adelic GL -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set Topology
open scoped CategoryTheory.MonObj CompactlySupported Pointwise

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

private abbrev GLG (F : Type u) [Field F] (n : ℕ) :=
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance glIsAffine (F : Type u) [Field F] (n : ℕ) : IsAffine (GLG F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance glSmooth (F : Type u) [Field F] (n : ℕ) : Smooth (GLG F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

section SliceBound

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLG F n)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

/-- A squared evaluation bound by compact-conjugate subgroup mass implies a polynomial
bound on each archimedean slice, with degree the real archimedean matrix dimension. -/
theorem generalLinear_sliceGrowth_of_compactConjugateBound
    (S : Set (AdelicGroupPoints F (GLG F n))) (hS : IsCompact S)
    (ψ : PositiveRationalQuotient F (GLG F n) T i → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hψ : ∀ x : AdelicGroupPoints F (GLG F n), ‖ψ (Quotient.mk _ x)‖ ^ 2 ≤
      L * (positiveRationalSubgroupHaarMeasure F (GLG F n) T i hi I e hc).real
        (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S))) :
    ∀ b : FiniteAdelicGL F n, ∃ C : ℝ, 0 ≤ C ∧ ∀ a : InfiniteAdelicGL F n,
      let x := (GeneralLinearGroupPoints.adelicHomeomorph F n).symm (AdelicGL.pair F n a b)
      ‖ψ (Quotient.mk _ x)‖ ≤ C * infiniteAdelicHilbertNorm F n a ^
        Module.finrank ℝ (ArchimedeanMatrix F n) := by
  intro b
  obtain ⟨B, hB, hmass⟩ := adelicGLPositiveRationalConjugateGrowth F n T i hi I e hc S hS b
  refine ⟨Real.sqrt (L * B), Real.sqrt_nonneg _, ?_⟩
  intro a
  let x := (GeneralLinearGroupPoints.adelicHomeomorph F n).symm (AdelicGL.pair F n a b)
  let d := Module.finrank ℝ (ArchimedeanMatrix F n)
  let H := infiniteAdelicHilbertNorm F n a
  have hH : 0 ≤ H := zero_le_one.trans (one_le_infiniteAdelicHilbertNorm F n a)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hH d))).mp
  change ‖ψ (Quotient.mk _ x)‖ ^ 2 ≤ (Real.sqrt (L * B) * H ^ d) ^ 2
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hL hB), ← pow_mul, mul_comm d 2, mul_assoc]
  exact (hψ x).trans (mul_le_mul_of_nonneg_left (hmass a) hL)

end SliceBound

/-- Given the actual continuous-representative assertion for compact convolution, it yields a
representative of polynomial growth on every fixed finite slice of the matrix group. -/
def GeneralLinearContinuousSmoothingGrowthStatement : Prop :=
  GroupSchemeQuotientL2ContinuousRepresentativeStatement.{u} →
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLG F n)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F (GLG F n))).IsMulRightInvariant],
    let μG : Measure (AdelicGroupPoints F (GLG F n)) := Measure.haar
    let μQ := positiveRationalQuotientHaarMeasure F (GLG F n) T i
    ∀ (f : C_c(AdelicGroupPoints F (GLG F n), ℂ)) (hf : Integrable f μG) (φ : Lp ℂ 2 μQ),
      ∃ ψ : C(PositiveRationalQuotient F (GLG F n) T i, ℂ),
        (haarQuotientL2IntegratedAction F (GLG F n) T i hi I e hc μG f hf φ :
          PositiveRationalQuotient F (GLG F n) T i → ℂ) =ᵐ[μQ] ψ ∧
        ∀ b : FiniteAdelicGL F n, ∃ C : ℝ, 0 ≤ C ∧ ∀ a : InfiniteAdelicGL F n,
          let x := (GeneralLinearGroupPoints.adelicHomeomorph F n).symm (AdelicGL.pair F n a b)
          ‖ψ (Quotient.mk _ x)‖ ≤ C * infiniteAdelicHilbertNorm F n a ^
            Module.finrank ℝ (ArchimedeanMatrix F n)

set_option maxHeartbeats 800000 in
/-- Bound the compact kernel globally and apply the slice bound to the product of supports. -/
theorem generalLinearContinuousSmoothingGrowth : GeneralLinearContinuousSmoothingGrowthStatement.{u} := by
  intro hrep F _ _ n T i hi _ I _ e hc _ μG μQ f hf φ
  obtain ⟨ψ, hψ, hψae, hψest⟩ := hrep F (GLG F n) T i hi I e hc f hf φ
  let K := tsupport f
  have hK : IsCompact K := f.hasCompactSupport
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn f.continuous.continuousOn
  let M' := max 0 M
  have hM' : 0 ≤ M' := le_max_left _ _
  have hbound (x : AdelicGroupPoints F (GLG F n)) : ‖f x‖ ≤ M' := by
    by_cases hx : x ∈ K
    · exact (hM x hx).trans (le_max_right _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact hM'
  let L := M' * (∫ a, ‖f a‖ ∂μG) * ‖φ‖ ^ 2
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg hM' (integral_nonneg fun _ => norm_nonneg _)) (sq_nonneg _)
  have hsq (x : AdelicGroupPoints F (GLG F n)) : ‖ψ (Quotient.mk _ x)‖ ^ 2 ≤
      L * (positiveRationalSubgroupHaarMeasure F (GLG F n) T i hi I e hc).real
        (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' (K * K⁻¹))) := by
    dsimp only [L]
    rw [mul_right_comm (M' * (∫ a, ‖f a‖ ∂μG))]
    exact hψest x M' hbound
  have hgrowth := generalLinear_sliceGrowth_of_compactConjugateBound F n T i hi I e hc
    (K * K⁻¹) (hK.mul hK.inv) ψ L hL hsq
  exact ⟨⟨ψ, hψ⟩, hψae, hgrowth⟩

end Langlands.Automorphic.GroupSchemeFunctions
