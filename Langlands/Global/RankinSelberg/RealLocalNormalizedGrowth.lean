import Langlands.Global.RankinSelberg.RealUniformContinuationReduction
import Langlands.Global.RankinSelberg.ArchimedeanRealPairFactor
import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction
import Langlands.LocalFactor.Archimedean.GammaStripGrowth

/-! # Entire normalizations with strip growth for the real Jacquet induction -/

noncomputable section

open Filter Set
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped NNReal Topology

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal

/-- The entire normalized pair for real block lists: two entire functions of exponential
growth on vertical strips that agree on a right half-plane with the given functions multiplied
by the reciprocal real pair `L`-factors, and satisfy the normalized functional equation at every
point. -/
def HasRealPairNormalizedGrowth (ds es dds ees : List RealBlock) (b : ℝˣ) (c : ℝ≥0)
    (hc : 0 < c) (sign : ℂ) (I Id : ℂ → ℂ) : Prop :=
  ∃ N Nd : ℂ → ℂ, Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
    HasStripExponentialGrowth N ∧ HasStripExponentialGrowth Nd ∧
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      N s = (realPairLFactor ds es).denominator s * I s ∧
      Nd s = (realPairLFactor dds ees).denominator s * Id s) ∧
    ∀ s : ℂ, Nd (1 - s) = sign * (realPairEpsilon ds es b c hc s : ℂ) * N s

namespace HasRealPairNormalizedGrowth

variable {ds es dds ees : List RealBlock} {b : ℝˣ} {c : ℝ≥0} {hc : 0 < c} {sign : ℂ}

/-- Agreement on a right half-plane suffices to transfer the normalized pair. -/
theorem congr {I Id I' Id' : ℂ → ℂ}
    (h : HasRealPairNormalizedGrowth ds es dds ees b c hc sign I Id) {τ : ℝ}
    (hI : ∀ s : ℂ, τ < s.re → I s = I' s) (hId : ∀ s : ℂ, τ < s.re → Id s = Id' s) :
    HasRealPairNormalizedGrowth ds es dds ees b c hc sign I' Id' := by
  obtain ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨σ, hR⟩, hFE⟩ := h
  refine ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨max σ τ, fun s hs => ?_⟩, hFE⟩
  have hσ : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hτ : τ < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  rw [← hI s hτ, ← hId s hτ]
  exact hR s hσ

/-- The zero pair has the zero normalization. -/
theorem zero : HasRealPairNormalizedGrowth ds es dds ees b c hc sign 0 0 :=
  ⟨0, 0, differentiable_const 0, differentiable_const 0, HasStripExponentialGrowth.const 0,
    HasStripExponentialGrowth.const 0, ⟨0, fun s _ => by simp⟩, fun s => by simp⟩

/-- Normalized pairs add. -/
theorem add {I Id J Jd : ℂ → ℂ}
    (h : HasRealPairNormalizedGrowth ds es dds ees b c hc sign I Id)
    (h' : HasRealPairNormalizedGrowth ds es dds ees b c hc sign J Jd) :
    HasRealPairNormalizedGrowth ds es dds ees b c hc sign (I + J) (Id + Jd) := by
  obtain ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨σ, hR⟩, hFE⟩ := h
  obtain ⟨M, Md, hM, hMd, hMg, hMdg, ⟨τ, hR'⟩, hFE'⟩ := h'
  refine ⟨N + M, Nd + Md, hN.add hM, hNd.add hMd, hNg.add hMg, hNdg.add hMdg,
    ⟨max σ τ, fun s hs => ?_⟩, fun s => ?_⟩
  · obtain ⟨h₁, h₂⟩ := hR s (lt_of_le_of_lt (le_max_left _ _) hs)
    obtain ⟨h₃, h₄⟩ := hR' s (lt_of_le_of_lt (le_max_right _ _) hs)
    simp only [Pi.add_apply, h₁, h₂, h₃, h₄]
    constructor <;> ring
  · simp only [Pi.add_apply, hFE, hFE']
    ring

/-- Normalized pairs are stable under a common scalar multiple. -/
theorem const_mul {I Id : ℂ → ℂ}
    (h : HasRealPairNormalizedGrowth ds es dds ees b c hc sign I Id) (z : ℂ) :
    HasRealPairNormalizedGrowth ds es dds ees b c hc sign (fun s => z * I s)
      (fun s => z * Id s) := by
  obtain ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨σ, hR⟩, hFE⟩ := h
  refine ⟨fun s => z * N s, fun s => z * Nd s, (differentiable_const z).mul hN,
    (differentiable_const z).mul hNd, hNg.const_mul z, hNdg.const_mul z,
    ⟨σ, fun s hs => ?_⟩, fun s => ?_⟩
  · obtain ⟨h₁, h₂⟩ := hR s hs
    simp only [h₁, h₂]
    constructor <;> ring
  · simp only [hFE]
    ring

/-- Finite sums of normalized pairs are normalized pairs. -/
theorem sum {ι : Type*} (S : Finset ι) (I Id : ι → ℂ → ℂ)
    (h : ∀ j ∈ S, HasRealPairNormalizedGrowth ds es dds ees b c hc sign (I j) (Id j)) :
    HasRealPairNormalizedGrowth ds es dds ees b c hc sign (fun s => ∑ j ∈ S, I j s)
      (fun s => ∑ j ∈ S, Id j s) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact zero
  | @insert j S hj ih =>
    have hS := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hj' := h j (Finset.mem_insert_self j S)
    have := hj'.add hS
    refine this.congr (τ := 0) (fun s _ => ?_) (fun s _ => ?_)
    · simp [Finset.sum_insert hj]
    · simp [Finset.sum_insert hj]

/-- A normalized pair gives the continuation package with the real pair factors: the two
normalizations divided by the reciprocal `L`-factors are meromorphic continuations, and the
multiplied-out functional equation holds at every point. -/
theorem continuationPackage {I Id : ℂ → ℂ}
    (h : HasRealPairNormalizedGrowth ds es dds ees b c hc sign I Id) :
    ContinuationPackage I Id (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
      (fun s => ((realPairLFactor dds ees).denominator s)⁻¹)
      (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign := by
  obtain ⟨N, Nd, hN, hNd, -, -, ⟨σ, hR⟩, hFE⟩ := h
  set P := realPairLFactor ds es
  set Pd := realPairLFactor dds ees
  obtain ⟨τ, hτ⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks ds es)
  obtain ⟨τd, hτd⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks dds ees)
  have hmero {F : ℂ → ℂ} (hF : Differentiable ℂ F) (Q : ReciprocalEntire) :
      MeromorphicOn (fun s => F s * (Q.denominator s)⁻¹) univ := fun s _ =>
    (hF.analyticAt s).meromorphicAt.mul (Q.entire.analyticAt s).meromorphicAt.inv
  refine ⟨max σ (max τ τd), fun s => N s * (P.denominator s)⁻¹,
    fun s => Nd s * (Pd.denominator s)⁻¹, hmero hN P, hmero hNd Pd, fun s hs => ?_,
    fun s hs => ?_, Eventually.of_forall fun s => ?_⟩
  · have hσ : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hP : P.denominator s ≠ 0 :=
      hτ s (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs)
    show I s = N s * (P.denominator s)⁻¹
    rw [(hR s hσ).1]
    field_simp
  · have hσ : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hPd : Pd.denominator s ≠ 0 :=
      hτd s (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs)
    show Id s = Nd s * (Pd.denominator s)⁻¹
    rw [(hR s hσ).2]
    field_simp
  · change (P.denominator s)⁻¹ * (Nd (1 - s) * (Pd.denominator (1 - s))⁻¹) =
      sign * (realPairEpsilon ds es b c hc s : ℂ) * (Pd.denominator (1 - s))⁻¹ *
        (N s * (P.denominator s)⁻¹)
    rw [hFE]
    ring

/-- The unequal-rank continuation package follows from a normalized pair for the exact unequal
integrals and the factors used by `UnequalContinuation`. -/
theorem unequalContinuation {r t : ℕ} {h : t < r} {a : ℝˣ} {D : RealQuotientMeasureData t}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ}
    (hN : HasRealPairNormalizedGrowth ds es dds ees b (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) sign
      (realUnequalIntegral h D W W') (realUnequalDualIntegral h a D W W')) :
    UnequalContinuation h a D W W' ds es dds ees b sign :=
  hN.continuationPackage

/-- The equal-rank continuation package follows from a normalized pair for the exact equal
integrals and the factors used by `EqualContinuation`. -/
theorem equalContinuation {r : ℕ} {a : ℝˣ} {D : RealQuotientMeasureData r}
    {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ}
    (hN : HasRealPairNormalizedGrowth ds es dds ees b (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) sign
      (realEqualIntegral D W W' Φ) (realEqualDualIntegral b D W W' Φ)) :
    EqualContinuation a b D W W' Φ ds es dds ees sign :=
  hN.continuationPackage

end HasRealPairNormalizedGrowth

private theorem eq_codiscrete_of_halfPlane {F G : ℂ → ℂ}
    (hF : MeromorphicOn F univ) (hG : MeromorphicOn G univ) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → F s = G s) : F =ᶠ[codiscrete ℂ] G := by
  let z : ℂ := (σ + 1 : ℝ)
  have hz : σ < z.re := by rw [Complex.ofReal_re]; linarith
  have hnear : ∀ᶠ s in 𝓝 z, σ < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hzero : (F - G) =ᶠ[𝓝[≠] z] 0 :=
    (hnear.filter_mono nhdsWithin_le_nhds).mono fun s hs => sub_eq_zero.mpr (h s hs)
  have ho := meromorphicOrderAt_eq_top_iff.mpr hzero
  refine eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mpr fun s => ?_
  have hs := (hF.sub hG).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ z) (mem_univ s) ho
  exact (eventuallyEq_iff_sub).mpr (meromorphicOrderAt_eq_top_iff.mp hs)

/-- Entire normalizations of the continuations in a continuation package satisfy the
normalized functional equation at every point. -/
theorem normalizedEquation_of_continuationPackage
    {ds es dds ees : List RealBlock} {b : ℝˣ} {c : ℝ≥0} {hc : 0 < c} {sign : ℂ}
    {I Id N Nd : ℂ → ℂ}
    (hP : ContinuationPackage I Id (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
      (fun s => ((realPairLFactor dds ees).denominator s)⁻¹)
      (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign)
    (hN : Differentiable ℂ N) (hNd : Differentiable ℂ Nd) {σ : ℝ}
    (hR : ∀ s : ℂ, σ < s.re →
      N s = (realPairLFactor ds es).denominator s * I s ∧
      Nd s = (realPairLFactor dds ees).denominator s * Id s) :
    ∀ s : ℂ, Nd (1 - s) = sign * (realPairEpsilon ds es b c hc s : ℂ) * N s := by
  obtain ⟨τ, M, Md, hM, hMd, hIM, hIdMd, hFE⟩ := hP
  set P := realPairLFactor ds es
  set Pd := realPairLFactor dds ees
  let E (s : ℂ) := (realPairEpsilon ds es b c hc s : ℂ)
  have hPm : MeromorphicOn P.denominator univ := fun s _ => (P.entire.analyticAt s).meromorphicAt
  have hPdm : MeromorphicOn Pd.denominator univ := fun s _ =>
    (Pd.entire.analyticAt s).meromorphicAt
  have hNM : N =ᶠ[codiscrete ℂ] fun s => P.denominator s * M s :=
    eq_codiscrete_of_halfPlane (fun s _ => (hN.analyticAt s).meromorphicAt) (hPm.mul hM)
      (max σ τ) fun s hs => by
        rw [(hR s (lt_of_le_of_lt (le_max_left _ _) hs)).1,
          hIM s (lt_of_le_of_lt (le_max_right _ _) hs)]
  have hNdM : Nd =ᶠ[codiscrete ℂ] fun s => Pd.denominator s * Md s :=
    eq_codiscrete_of_halfPlane (fun s _ => (hNd.analyticAt s).meromorphicAt) (hPdm.mul hMd)
      (max σ τ) fun s hs => by
        rw [(hR s (lt_of_le_of_lt (le_max_left _ _) hs)).2,
          hIdMd s (lt_of_le_of_lt (le_max_right _ _) hs)]
  have hPne : ∀ᶠ s in codiscrete ℂ, P.denominator s ≠ 0 :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr P.denominator_eventually_ne_zero
  have hPdne : ∀ᶠ s in codiscrete ℂ, Pd.denominator s ≠ 0 :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr Pd.denominator_eventually_ne_zero
  have he : (fun s : ℂ => Nd (1 - s)) =ᶠ[codiscrete ℂ] fun s => sign * E s * N s := by
    filter_upwards [hFE, hNM, CuspidalPairPartialGammaGlobal.eventually_codiscrete_one_sub hNdM,
      hPne, CuspidalPairPartialGammaGlobal.eventually_codiscrete_one_sub hPdne]
      with s h hN' hNd' hp hpd
    change (P.denominator s)⁻¹ * Md (1 - s) = sign * E s * (Pd.denominator (1 - s))⁻¹ * M s
      at h
    rw [hN', hNd']
    calc
      _ = Pd.denominator (1 - s) * (P.denominator s * ((P.denominator s)⁻¹ * Md (1 - s))) := by
        rw [← mul_assoc (P.denominator s), mul_inv_cancel₀ hp, one_mul]
      _ = _ := by rw [h]; field_simp
  have hE : Continuous E := (differentiable_realEpsilon _ b c hc).continuous
  have hleft : Continuous (fun s : ℂ => Nd (1 - s)) :=
    hNd.continuous.comp (continuous_const.sub continuous_id)
  have hright : Continuous (fun s : ℂ => sign * E s * N s) :=
    (continuous_const.mul hE).mul hN.continuous
  intro s
  exact tendsto_nhds_unique_of_eventuallyEq hleft.continuousAt.continuousWithinAt
    hright.continuousAt.continuousWithinAt (he.filter_mono (nhdsNE_le_codiscrete s))

/-- A continuation package together with entire normalizations of strip growth that agree with
the normalized integrals on a right half-plane gives the normalized pair. -/
theorem hasRealPairNormalizedGrowth_of_continuationPackage
    {ds es dds ees : List RealBlock} {b : ℝˣ} {c : ℝ≥0} {hc : 0 < c} {sign : ℂ}
    {I Id N Nd : ℂ → ℂ}
    (hP : ContinuationPackage I Id (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
      (fun s => ((realPairLFactor dds ees).denominator s)⁻¹)
      (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign)
    (hN : Differentiable ℂ N) (hNd : Differentiable ℂ Nd)
    (hNg : HasStripExponentialGrowth N) (hNdg : HasStripExponentialGrowth Nd) {σ : ℝ}
    (hR : ∀ s : ℂ, σ < s.re →
      N s = (realPairLFactor ds es).denominator s * I s ∧
      Nd s = (realPairLFactor dds ees).denominator s * Id s) :
    HasRealPairNormalizedGrowth ds es dds ees b c hc sign I Id :=
  ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨σ, hR⟩,
    normalizedEquation_of_continuationPackage hP hN hNd hR⟩

end Langlands.Global.RankinSelbergGlobal.RealJacquet
