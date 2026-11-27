import Langlands.Global.AdelicRationalConjugateCountingAllPointsProof
import Langlands.Automorphic.GroupSchemePositiveQuotientL2Smoothing
import Langlands.Automorphic.GroupSchemeQuotientMassBound
import Langlands.Automorphic.GroupSchemeQuotientL2ContinuousRepresentativeProof

/-! # Global growth of compact convolutions on the positive rational quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal Pointwise CompactlySupported

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

local notation "A" => AdelicGroupPoints F G
local notation "Γ" => rationalNormOneSubgroup F G
local notation "μH" => positiveRationalSubgroupHaarMeasure F G T i hi I e hc

/-- The positive-rational subgroup mass of a conjugated compact set is bounded by a
power of the adelic height at every adelic point. -/
theorem adelicPositiveRationalConjugateGrowth_allPoints (hN : 0 < N) (hrho : IsClosedSubgroup rho) :
    ∃ d : ℕ, ∀ (S : Set A), IsCompact S → ∃ B : ℝ, 0 ≤ B ∧ ∀ x : A,
      (μH).real (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S)) ≤ B * adelicHeight F G rho x ^ d := by
  classical
  obtain ⟨d, hCount⟩ := adelicRationalConjugateCountingAllPoints F G N rho hN hrho
  refine ⟨d, fun S hS => ?_⟩
  let π₀ := positiveFactor F G T i hi I e
  let π₁ := normOneProjection F G T i hi I e hc
  let E := positiveRationalDecomposition F G T i hi I e hc
  let μ₀ := normalizedPositiveHaarMeasure F G T i hi I e hc
  let μ₁ : Measure Γ := Measure.count
  let S₀ := π₀ '' S
  let S₁ := (fun s : A => (π₁ s).val) '' S
  have hS₀ : IsCompact S₀ := hS.image π₀.continuous
  have hS₁ : IsCompact S₁ := hS.image (continuous_subtype_val.comp π₁.continuous)
  obtain ⟨C, hC, hCount₁⟩ := hCount S₁ hS₁
  let : μ₀.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure F G T i hi I e hc
  have hμ₀ : μ₀ S₀ ≠ ∞ := hS₀.measure_lt_top.ne
  refine ⟨(μ₀ S₀).toReal * C, mul_nonneg ENNReal.toReal_nonneg hC, fun x => ?_⟩
  let U : Set (positiveRationalSubgroup F G T i) := Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S)
  let P := (rationalSubgroup F G : Set A) ∩ ((fun s => x * s * x⁻¹) '' S₁)
  let j : Γ → A := fun r => r.val.val
  have hj : Function.Injective j := fun _ _ h => Subtype.ext (Subtype.ext h)
  let Q := j ⁻¹' P
  obtain ⟨hP, hPb⟩ := hCount₁ x
  change P.Finite at hP
  have hQ : Q.Finite := hP.preimage hj.injOn
  have hQP : Q.ncard ≤ P.ncard := Set.ncard_le_ncard_of_injOn j (fun _ hq => hq) hj.injOn hP
  have hpos (s : A) : π₀ (x * s * x⁻¹) = π₀ s := by
    simp only [map_mul, map_inv]
    rw [mul_comm (π₀ x) (π₀ s), mul_assoc, mul_inv_cancel, mul_one]
  have hproj (s : A) : (π₁ (x * s * x⁻¹)).val = x * (π₁ s).val * x⁻¹ := by
    change (normOneFactor F G T i hi I e (x * s * x⁻¹)).val =
      x * (normOneFactor F G T i hi I e s).val * x⁻¹
    simp only [normOneFactor_val]
    change (positivePointMap F G T i (π₀ (x * s * x⁻¹)))⁻¹ * (x * s * x⁻¹) =
      x * ((positivePointMap F G T i (π₀ s))⁻¹ * s) * x⁻¹
    rw [hpos]
    let z := positivePointMap F G T i (π₀ s)
    have hz : Commute z x := positivePointMap_commute F G T i hc (π₀ s) x
    change z⁻¹ * (x * s * x⁻¹) = x * (z⁻¹ * s) * x⁻¹
    rw [← mul_assoc z⁻¹, ← mul_assoc z⁻¹, hz.inv_left.eq, mul_assoc x z⁻¹]
  have hsub : E ⁻¹' U ⊆ S₀ ×ˢ Q := by
    rintro p ⟨s, hs, he⟩
    have hp : (E p).val = positivePointMap F G T i p.1 * p.2.val.val := rfl
    have hp₀ : π₀ (E p).val = p.1 := positiveFactor_mul_normOne F G T i hi I e p.1 p.2.val
    have hp₁ : π₁ (E p).val = p.2.val := by
      rw [hp, map_mul, normOneProjection_positivePointMap, normOneProjection_normOne, one_mul]
    refine ⟨⟨s, hs, (hpos s).symm.trans ((congrArg π₀ he).trans hp₀)⟩, ?_⟩
    have hr : j p.2 ∈ rationalSubgroup F G := by
      obtain ⟨r, hr⟩ := p.2.2
      exact ⟨r, congrArg Subtype.val hr⟩
    refine ⟨hr, (π₁ s).val, ⟨s, hs, rfl⟩, ?_⟩
    exact (hproj s).symm.trans ((congrArg (fun s : A => (π₁ s).val) he).trans (congrArg Subtype.val hp₁))
  have hpres : MeasurePreserving E.toHomeomorph.toMeasurableEquiv (μ₀.prod μ₁) μH :=
    measurePreserving_positiveRationalDecomposition F G T i hi I e hc
  have hcnt : μ₁ Q = Q.ncard := by
    rw [Set.ncard_eq_toFinset_card Q hQ]
    exact Measure.count_apply_finite Q hQ
  have htop : μ₀ S₀ * μ₁ Q ≠ ∞ := ENNReal.mul_ne_top hμ₀ (by rw [hcnt]; exact ENNReal.natCast_ne_top _)
  have hle : μH U ≤ μ₀ S₀ * μ₁ Q := by
    rw [← hpres.measure_preimage_equiv U, ← Measure.prod_prod]
    exact measure_mono hsub
  change (μH U).toReal ≤ _
  calc
    _ ≤ (μ₀ S₀ * μ₁ Q).toReal := ENNReal.toReal_mono htop hle
    _ = (μ₀ S₀).toReal * (Q.ncard : ℝ) := by rw [ENNReal.toReal_mul, hcnt, ENNReal.toReal_natCast]
    _ ≤ (μ₀ S₀).toReal * (P.ncard : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hQP) ENNReal.toReal_nonneg
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hPb ENNReal.toReal_nonneg

end Langlands.Global.PositiveRealTorus

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global AdelicGroupPoints PositiveRealTorus Langlands.GroupScheme RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints F G
local notation "Γ" => positiveRationalSubgroup F G T i
local notation "Q" => PositiveRationalQuotient F G T i
local notation "dq" => positiveRationalQuotientHaarMeasure F G T i
local notation "dg" => (Measure.haar : Measure A)

include hi I e hc in
/-- A compact smooth test kernel gives a smooth representative of the integrated right
action on the positive rational quotient. That representative has global moderate growth. -/
theorem positiveQuotientLpSmoothing_smooth_moderateGrowth {d N : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) (hrho : IsClosedSubgroup rho) {h : A → ℂ} (hh : IsAdelicTestFunction F G h)
    (v : Lp ℂ 2 dq) :
    IsAdelicSmoothFunction F G (positiveQuotientLpSmoothing T i h v) ∧
      HasModerateGrowthFunction F G rho (positiveQuotientLpSmoothing T i h v) := by
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := haarQuotientMeasure_isOpenPosMeasure F G T i hi I e hc
  obtain ⟨m, hMass⟩ := adelicPositiveRationalConjugateGrowth_allPoints rho T i hi I e hc hN hrho
  obtain ⟨_, hsmooth'⟩ := groupSchemePositiveQuotientL2Smoothing T i hsmooth rho
    hi I e hc hN hrho
  have hsm := (hsmooth' h hh).1 v
  refine ⟨hsm, ?_⟩
  let f : C_c(A, ℂ) := ⟨⟨h, hh.1.1⟩, hh.2.1⟩
  have hf : Integrable f dg := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  obtain ⟨ψ, C, hC, hψae, hψ⟩ := exists_quotientMassBound_representative F G T i hi I e hc
    groupSchemeQuotientL2ContinuousRepresentative f hf v
  let φ := positiveQuotientLpSmoothing T i h v
  have hInv : ∀ (r : Γ) (x : A), φ (r.val * x) = φ x := positiveQuotientLpSmoothing_invariant T i h v
  let φQ : Q → ℂ := LeftCosetSpace.lift Γ φ hInv
  have hφc : Continuous φQ := hsm.1.quotient_lift _
  have hφae : (haarQuotientL2IntegratedAction F G T i hi I e hc dg f hf v : Q → ℂ) =ᵐ[dq] φQ :=
    positiveQuotientLpSmoothing_ae_eq T i hi I e hc h hf v
  have heq : φQ = ψ := Measure.eq_of_ae_eq (hφae.symm.trans hψae) hφc ψ.continuous
  obtain ⟨B, hB, hBmass⟩ := hMass _ (f.hasCompactSupport.mul f.hasCompactSupport.inv)
  let c := Real.sqrt (C * B)
  let scale : ℝ := (N : ℝ) ^ (∑ t : NumberField.InfinitePlace F, t.mult)
  have hscale : 0 < scale := pow_pos (Nat.cast_pos.mpr hN) _
  refine ⟨(c + 1) * scale ^ m, by positivity, (m : ℝ), fun x => ?_⟩
  let H := adelicHeight F G rho x
  have hH : 1 ≤ H := one_le_adelicHeight F G rho hN x
  have hHpow : 1 ≤ H ^ m := one_le_pow₀ hH
  have hsq : ‖φ x‖ ^ 2 ≤ C * (B * H ^ m) := by
    change ‖φQ (LeftCosetSpace.mk Γ x)‖ ^ 2 ≤ _
    rw [heq]
    exact (hψ x).trans (mul_le_mul_of_nonneg_left (hBmass x) hC)
  have hb : ‖φ x‖ ≤ c * H ^ m := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hC hB), mul_assoc]
    refine hsq.trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact mul_le_mul_of_nonneg_left (le_self_pow₀ hHpow (by decide)) hB
  calc
    _ ≤ (c + 1) * H ^ m := hb.trans (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hHpow))
    _ = _ := by
      rw [Real.rpow_natCast, mul_assoc, ← mul_pow]
      congr 1
      exact congrArg (· ^ m) (adelicHeight_eq_scalar_mul_sourceNorm F G rho x)

end Langlands.Automorphic.GroupSchemeFunctions
