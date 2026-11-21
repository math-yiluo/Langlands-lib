import Langlands.Global.Factors.FiniteComparisonProof
import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction
import Langlands.Global.RankinSelberg.ComplexLocalEqualJacquetExpansion
import Langlands.LocalFactor.Archimedean.GammaStripGrowth

/-! # Entire normalizations with strip growth for the complex Jacquet induction -/

noncomputable section

open Filter Set
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped NNReal Topology

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

/-- The entire normalized pair, with strip growth and agreement with the two
given functions on a right half-plane. -/
def HasComplexPairNormalizedGrowth (ds es : List ComplexCharacterData) (a : ℂˣ) (c : ℂ)
    (I Id : ℂ → ℂ) : Prop :=
  ∃ N Nd : ℂ → ℂ, Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
    HasStripExponentialGrowth N ∧ HasStripExponentialGrowth Nd ∧
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      N s = (complexPairLFactor ds es).denominator s * I s ∧
      Nd s = (complexPairLFactor (ds.map ComplexCharacterData.inv)
        (es.map ComplexCharacterData.inv)).denominator s * Id s) ∧
    ∀ s : ℂ, Nd (1 - s) = c *
      (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s

/-- At parameter one the pair epsilon factor is independent of the spectral parameter. -/
theorem complexPairEpsilon_one (ds es : List ComplexCharacterData) (s : ℂ) :
    complexPairEpsilon ds es 1 ‖((1 : ℂˣ) : ℂ)‖₊ (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s =
      complexPairStandardEpsilon ds es := by
  simpa only [complexPairEpsilon, complexPairStandardEpsilon, Units.val_one, nnnorm_one] using
    complexEpsilon_standard (ds := complexPairBlocks ds es) (s := s)

/-- At parameter minus one the pair epsilon factor is also constant. -/
theorem complexPairEpsilon_neg_one (ds es : List ComplexCharacterData) (s : ℂ) :
    (complexPairEpsilon ds es (-1) ‖((-1 : ℂˣ) : ℂ)‖₊
      (nnnorm_pos.mpr (neg_ne_zero.mpr (1 : ℂˣ).ne_zero)) s : ℂ) =
      (complexCentralSign ds ^ es.length * complexCentralSign es ^ ds.length) *
        complexPairStandardEpsilon ds es := by
  have h := pair_epsilon_neg ds es (1 : ℂˣ)
    ‖((1 : ℂˣ) : ℂ)‖₊ (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s
  simpa only [Units.val_neg, nnnorm_neg, complexPairEpsilon_one] using h

private theorem eq_codiscrete_of_meromorphic_halfPlane {F G : ℂ → ℂ}
    (hF : Meromorphic F) (hG : Meromorphic G) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → F s = G s) : F =ᶠ[codiscrete ℂ] G := by
  exact eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mpr
    (Langlands.Global.FunctionalEquationComparison.eq_on_halfplane_meromorphicEq hF hG h)

/-- When both normalized half-plane functions are entire, the meromorphic
equation of the original continuations gives the normalized equation everywhere. -/
theorem normalizedEquation_of_pairMeromorphicEquation
    {ds es : List ComplexCharacterData} {a : ℂˣ} {c : ℂ} {M Md N Nd : ℂ → ℂ}
    (hM : Meromorphic M) (hMd : Meromorphic Md)
    (hFE : PairMeromorphicEquation ds es a c M Md)
    (hN : Differentiable ℂ N) (hNd : Differentiable ℂ Nd)
    (hE : Continuous (fun s : ℂ =>
      (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)))
    {σ : ℝ} (hR : ∀ s : ℂ, σ < s.re →
      N s = (complexPairLFactor ds es).denominator s * M s ∧
      Nd s = (complexPairLFactor (ds.map ComplexCharacterData.inv)
        (es.map ComplexCharacterData.inv)).denominator s * Md s) :
    ∀ s : ℂ, Nd (1 - s) = c *
      (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s := by
  let L := complexPairLFactor ds es
  let Ld := complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)
  let E (s : ℂ) := (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)
  have hL : Meromorphic L.denominator := fun s => (L.entire.analyticAt s).meromorphicAt
  have hLd : Meromorphic Ld.denominator := fun s => (Ld.entire.analyticAt s).meromorphicAt
  have hNL : N =ᶠ[codiscrete ℂ] fun s => L.denominator s * M s :=
    eq_codiscrete_of_meromorphic_halfPlane (fun s => (hN.analyticAt s).meromorphicAt)
      (hL.mul hM)
      σ (fun s hs => (hR s hs).1)
  have hNdL : Nd =ᶠ[codiscrete ℂ] fun s => Ld.denominator s * Md s :=
    eq_codiscrete_of_meromorphic_halfPlane (fun s => (hNd.analyticAt s).meromorphicAt)
      (hLd.mul hMd)
      σ (fun s hs => (hR s hs).2)
  have hLp : ∀ᶠ s in codiscrete ℂ, L.denominator s ≠ 0 :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr L.denominator_eventually_ne_zero
  have hLdp : ∀ᶠ s in codiscrete ℂ, Ld.denominator s ≠ 0 :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr Ld.denominator_eventually_ne_zero
  have he : (fun s : ℂ => Nd (1 - s)) =ᶠ[codiscrete ℂ] fun s => c * E s * N s := by
    filter_upwards [hFE, hNL, CuspidalPairPartialGammaGlobal.eventually_codiscrete_one_sub hNdL,
      hLp, CuspidalPairPartialGammaGlobal.eventually_codiscrete_one_sub hLdp] with s h hN' hNd' hP hD
    change (L.denominator s)⁻¹ * Md (1 - s) = c * E s * (Ld.denominator (1 - s))⁻¹ * M s at h
    rw [hN', hNd']
    calc
      _ = Ld.denominator (1 - s) * (L.denominator s * ((L.denominator s)⁻¹ * Md (1 - s))) := by
        rw [← mul_assoc (L.denominator s), mul_inv_cancel₀ hP, one_mul]
      _ = _ := by rw [h]; field_simp [hD]
  have hleft : Continuous (fun s : ℂ => Nd (1 - s)) :=
    hNd.continuous.comp (continuous_const.sub continuous_id)
  have hright : Continuous (fun s : ℂ => c * E s * N s) :=
    (continuous_const.mul hE).mul hN.continuous
  intro s
  have h₁ : Tendsto (fun t : ℂ => Nd (1 - t)) (𝓝[≠] s) (𝓝 (Nd (1 - s))) :=
    hleft.continuousAt.continuousWithinAt
  have h₂ : Tendsto (fun t : ℂ => c * E t * N t) (𝓝[≠] s) (𝓝 (c * E s * N s)) :=
    hright.continuousAt.continuousWithinAt
  exact tendsto_nhds_unique_of_eventuallyEq h₁ h₂ (he.filter_mono (nhdsNE_le_codiscrete s))

/-- The normalized functional equation follows from a meromorphic equation
and entire normalizations matching on the right. -/
def ComplexLocalNormalizedGrowthBridgeStatement : Prop :=
  ∀ (ds es : List ComplexCharacterData) (a : ℂˣ) (c : ℂ) (M Md N Nd : ℂ → ℂ),
    Meromorphic M → Meromorphic Md → PairMeromorphicEquation ds es a c M Md →
    Differentiable ℂ N → Differentiable ℂ Nd →
    Continuous (fun s : ℂ =>
      (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)) →
    ∀ σ : ℝ, (∀ s : ℂ, σ < s.re →
      N s = (complexPairLFactor ds es).denominator s * M s ∧
      Nd s = (complexPairLFactor (ds.map ComplexCharacterData.inv)
        (es.map ComplexCharacterData.inv)).denominator s * Md s) →
    ∀ s : ℂ, Nd (1 - s) = c *
      (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s

theorem complexLocalNormalizedGrowthBridge : ComplexLocalNormalizedGrowthBridgeStatement :=
  fun _ _ _ _ _ _ _ _ hM hMd hFE hN hNd hE _ hR =>
    normalizedEquation_of_pairMeromorphicEquation hM hMd hFE hN hNd hE hR

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
