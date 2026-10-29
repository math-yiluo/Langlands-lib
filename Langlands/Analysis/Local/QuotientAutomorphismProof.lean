import Langlands.Analysis.Local.QuotientAutomorphismStatement
import Langlands.Analysis.Local.QuotientPositiveLifting
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Compatible quotient measures under group automorphisms

A continuous automorphism preserving a closed subgroup scales every compatible
quotient measure by the ratio of the subgroup and ambient Haar moduli. Real
test functions on the quotient are lifted by the published positive lifting,
the two Haar changes of variables give the factor, and compact-test
extensionality identifies the regular measures.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal CompactlySupported

universe uG

/-- Real Haar change of variables along a continuous automorphism. -/
theorem mulEquivHaarChar_mul_integral_comp {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsHaarMeasure μ] [μ.Regular] (φ : K ≃ₜ* K) (F : K → ℝ) :
    (mulEquivHaarChar φ : ℝ) * ∫ x, F (φ x) ∂μ = ∫ x, F x ∂μ := by
  have hmap : (∫ x, F x ∂μ.map φ) = ∫ x, F (φ x) ∂μ :=
    integral_map_equiv φ.toHomeomorph.toMeasurableEquiv F
  have h := mulEquivHaarChar_smul_integral_map μ (f := F) φ
  rw [NNReal.smul_def, smul_eq_mul, hmap] at h
  exact h

section Compatible

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {H : Subgroup G} [MeasurableSpace H] [BorelSpace H]
variable {μG : Measure G} {μH : Measure H} [IsMulRightInvariant μH]
variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]

omit [BorelSpace G] [BorelSpace (LeftQuotient H)] in
/-- The complex Weil formula of a compatible measure, for real test functions. -/
theorem IsCompatible.integral_quotientAverageReal {ν : Measure (LeftQuotient H)}
    (hν : IsCompatible H μG μH ν) (f : G → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    (∫ q, quotientAverageReal H μH f q ∂ν) = ∫ g, f g ∂μG := by
  have h := hν.integral_formula (fun g => (f g : ℂ)) (Complex.continuous_ofReal.comp hf)
    (hc.comp_left Complex.ofReal_zero)
  simp_rw [quotientAverage_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h

end Compatible

section Scaling

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
variable [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
variable {μG : Measure G} {μH : Measure H}
  [IsHaarMeasure μG] [μG.Regular] [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
variable {ν : Measure (LeftQuotient H)}
variable (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ H ↔ x ∈ H)

omit [BorelSpace (LeftQuotient H)] in
include hH in
/-- Compact real tests read through the quotient automorphism integrate to
`δH / δG` times their integral. -/
theorem IsCompatible.integral_comp_quotientAutomorphism (hν : IsCompatible H μG μH ν)
    (φ : C_c(LeftQuotient H, ℝ)) :
    (∫ q, φ (quotientAutomorphism H α hα q) ∂ν) =
      ((mulEquivHaarChar (subgroupAutomorphism H α hα) : ℝ) / (mulEquivHaarChar α : ℝ)) *
        ∫ q, φ q ∂ν := by
  obtain ⟨f, hf, -⟩ := realQuotientPositiveLifting H hH μH φ
  have hφ : ∀ q, φ q = quotientAverageReal H μH f q := by
    intro q
    induction q using Quotient.inductionOn with
    | h g => exact (hf g).symm
  have hφα : ∀ q, φ (quotientAutomorphism H α hα q) =
      (mulEquivHaarChar (subgroupAutomorphism H α hα) : ℝ) *
        quotientAverageReal H μH (fun x => f (α x)) q := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      have key := mulEquivHaarChar_mul_integral_comp μH (subgroupAutomorphism H α hα)
        (fun h : H => f (h.val * α g))
      simp only [subgroupAutomorphism_apply, ← map_mul] at key
      rw [quotientAutomorphism_mk, ← hf (α g), quotientAverageReal_mk, ← key]
  have hG := mulEquivHaarChar_mul_integral_comp μG α f
  have hfint := hν.integral_quotientAverageReal f f.continuous f.hasCompactSupport
  have hαint := hν.integral_quotientAverageReal (fun x => f (α x))
    (f.continuous.comp α.continuous) (f.hasCompactSupport.comp_homeomorph α.toHomeomorph)
  have hδG : (mulEquivHaarChar α : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (mulEquivHaarChar_pos α)).ne'
  simp_rw [hφα, hφ]
  rw [integral_const_mul, hαint, hfint, ← hG]
  field_simp

include hH in
/-- The pushforward of a compatible measure by the quotient automorphism. -/
theorem IsCompatible.map_quotientAutomorphism (hν : IsCompatible H μG μH ν) :
    Measure.map (quotientAutomorphism H α hα) ν =
      (((mulEquivHaarChar (subgroupAutomorphism H α hα) / mulEquivHaarChar α : ℝ≥0)) :
        ℝ≥0∞) • ν := by
  have := leftQuotient_t2Space H hH
  have := leftQuotient_locallyCompactSpace (G := G) H
  have : ν.Regular := hν.regular
  have : (Measure.map (quotientAutomorphism H α hα) ν).Regular :=
    Measure.Regular.map (quotientAutomorphism H α hα)
  have : ((((mulEquivHaarChar (subgroupAutomorphism H α hα) / mulEquivHaarChar α : ℝ≥0)) :
      ℝ≥0∞) • ν).Regular := Measure.Regular.smul ENNReal.coe_ne_top
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  have hmap : (∫ q, φ q ∂Measure.map (quotientAutomorphism H α hα) ν) =
      ∫ q, φ (quotientAutomorphism H α hα q) ∂ν :=
    integral_map_equiv (quotientAutomorphism H α hα).toMeasurableEquiv φ
  rw [hmap, integral_smul_measure, ENNReal.coe_toReal, NNReal.coe_div, smul_eq_mul]
  exact hν.integral_comp_quotientAutomorphism H hH α hα φ

end Scaling

/-- Every compatible quotient measure is scaled by `δH / δG` under the
automorphism of the left quotient induced by a continuous automorphism
preserving the closed subgroup, and arbitrary integrands pulled back by the
inverse automorphism pick up `δG / δH`. -/
theorem compatibleQuotientAutomorphismScaling :
    CompatibleQuotientAutomorphismScaling.{uG} := by
  intro G _ _ _ _ _ _ _ H hH _ _ μG μH _ _ _ _ _ _ _ _ ν hν α hα
  have : LocallyCompactSpace H := hH.locallyCompactSpace
  intro αH αQ δG δH
  have hmap : Measure.map αQ ν = ((δH / δG : ℝ≥0) : ℝ≥0∞) • ν :=
    hν.map_quotientAutomorphism H hH α hα
  refine ⟨hmap, fun f => ?_⟩
  have hδG : δG ≠ 0 := (mulEquivHaarChar_pos α).ne'
  have hδH : δH ≠ 0 := (mulEquivHaarChar_pos αH).ne'
  have h1 : (∫ q, f (αQ.symm q) ∂Measure.map αQ ν) = ∫ q, f q ∂ν := by
    refine (integral_map_equiv αQ.toMeasurableEquiv (fun q => f (αQ.symm q))).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    exact congrArg f (αQ.symm_apply_apply q)
  rw [hmap, integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul] at h1
  have hprod : (δG / δH : ℝ≥0) * (δH / δG) = 1 := by
    rw [div_mul_div_comm, mul_comm δG δH, div_self (mul_ne_zero hδH hδG)]
  rw [← h1, ← mul_assoc, ← Complex.ofReal_mul, ← NNReal.coe_mul, hprod, NNReal.coe_one,
    Complex.ofReal_one, one_mul]

end Langlands.QuotientIntegration
