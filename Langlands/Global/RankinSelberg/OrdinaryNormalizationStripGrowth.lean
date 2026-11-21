import Langlands.Automorphic.AssociatedGammaCuspidalEquation
import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization
import Langlands.LocalFactor.Archimedean.GammaStripGrowth
import Langlands.Representation.RankinSelberg.NormalizedZetaCombination

/-! # Strip growth of normalized ordinary local integrals -/

noncomputable section

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Langlands.Global.RankinSelbergGlobal

open LocalFactor LocalFactor.Archimedean

private theorem stripGrowth_finset_prod {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ S, HasStripExponentialGrowth (f i)) :
    HasStripExponentialGrowth (fun s => ∏ i ∈ S, f i s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using HasStripExponentialGrowth.const 1
  | insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i S)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem stripGrowth_of_eventuallyEq_codiscrete {f g : ℂ → ℂ}
    (hf : Continuous f) (hg : HasStripExponentialGrowth g) (he : f =ᶠ[codiscrete ℂ] g) :
    HasStripExponentialGrowth f := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hB⟩ := hg (a - 1) (b + 1)
  refine ⟨C, K, T + 1, hC, hK, fun s ha hb ht => ?_⟩
  have hl : a - 1 < s.re := (sub_lt_self _ zero_lt_one).trans_le ha
  have hr : s.re < b + 1 := hb.trans_lt (lt_add_one _)
  have hT : T < |s.im| := (lt_add_one _).trans_le ht
  have hnear : ∀ᶠ z : ℂ in 𝓝 s, a - 1 < z.re ∧ z.re < b + 1 ∧ T < |z.im| := by
    have hopen : IsOpen {z : ℂ | a - 1 < z.re ∧ z.re < b + 1 ∧ T < |z.im|} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im.abs))
    exact hopen.mem_nhds ⟨hl, hr, hT⟩
  have hcont : Continuous (fun s : ℂ => C * Real.exp (K * |s.im|)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul Complex.continuous_im.abs))
  have hevent : ∀ᶠ z : ℂ in 𝓝[≠] s, ‖f z‖ ≤ C * Real.exp (K * |z.im|) := by
    filter_upwards [he.filter_mono (nhdsNE_le_codiscrete s),
      hnear.filter_mono nhdsWithin_le_nhds] with z hz hz'
    rw [hz]
    exact hB z hz'.1.le hz'.2.1.le hz'.2.2.le
  exact le_of_tendsto_of_tendsto (hf.norm.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hevent

/-- A raw meromorphic continuation of exponential strip growth gives the same
growth property for the entire normalized integral, when the reciprocal
L-denominator has exponential strip growth. -/
theorem OrdinaryIntegralNormalization.stripGrowth_of_meromorphic {I M : ℂ → ℂ}
    {L : ReciprocalEntire}
    (N : OrdinaryIntegralNormalization I (fun s => (L.denominator s)⁻¹))
    (hM : MeromorphicOn M univ) (hMg : HasStripExponentialGrowth M)
    (hLg : HasStripExponentialGrowth L.denominator)
    (hL : ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → L.denominator s ≠ 0)
    (hI : ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → I s = M s) :
    HasStripExponentialGrowth N.value := by
  obtain ⟨a, ha⟩ := N.eq_on_right
  obtain ⟨b, hb⟩ := hL
  obtain ⟨c, hc⟩ := hI
  let t := max (max a b) c
  have hEq (s : ℂ) (hs : t < s.re) : N.value s = M s * L.denominator s := by
    have hs' := (le_max_left (max a b) c).trans_lt hs
    have hn := hb s ((le_max_right a b).trans_lt hs')
    have he := ha s ((le_max_left a b).trans_lt hs')
    rw [hc s ((le_max_right (max a b) c).trans_lt hs)] at he
    rw [he, mul_assoc, inv_mul_cancel₀ hn, mul_one]
  let z : ℂ := (t + 1 : ℝ)
  have hz : t < z.re := by change t < t + 1; linarith
  have hz₀ : (N.value - M * L.denominator) =ᶠ[𝓝[≠] z] 0 := by
    have hnear : ∀ᶠ s in 𝓝 z, t < (s : ℂ).re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with s hs
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.zero_apply, hEq s hs, sub_self]
  have hN : MeromorphicOn N.value univ := fun s hs => (N.analytic s hs).meromorphicAt
  have hD : MeromorphicOn L.denominator univ := fun s _ => (L.entire.analyticAt s).meromorphicAt
  have hDiff := hN.sub (hM.mul hD)
  have ho := meromorphicOrderAt_eq_top_iff.mpr hz₀
  have he : N.value =ᶠ[codiscrete ℂ] M * L.denominator := by
    refine eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mpr (fun s => ?_)
    have hs := hDiff.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (mem_univ z) (mem_univ s) ho
    exact (eventuallyEq_iff_sub).mpr (meromorphicOrderAt_eq_top_iff.mp hs)
  exact stripGrowth_of_eventuallyEq_codiscrete (continuous_iff_continuousAt.mpr fun s =>
    (N.analytic s (mem_univ s)).continuousAt) (hMg.mul hLg) he

open FunctionalEquationComparison.CompletedEquationAdapter

/-- Specialization to the real pair Gamma factors. -/
theorem OrdinaryIntegralNormalization.stripGrowth_realPair {I M : ℂ → ℂ}
    {d d' : List RealBlock}
    (N : OrdinaryIntegralNormalization I (fun s => ((realPairLFactor d d').denominator s)⁻¹))
    (hM : MeromorphicOn M univ) (hMg : HasStripExponentialGrowth M)
    (hI : ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → I s = M s) :
    HasStripExponentialGrowth N.value :=
  N.stripGrowth_of_meromorphic hM hMg (stripGrowth_realPairLFactor_denominator d d')
    (realPairLFactor_denominator_ne_zero d d') hI

/-- Specialization to the complex pair Gamma factors. -/
theorem OrdinaryIntegralNormalization.stripGrowth_complexPair {I M : ℂ → ℂ}
    {d d' : List ComplexCharacterData}
    (N : OrdinaryIntegralNormalization I (fun s => ((complexPairLFactor d d').denominator s)⁻¹))
    (hM : MeromorphicOn M univ) (hMg : HasStripExponentialGrowth M)
    (hI : ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → I s = M s) :
    HasStripExponentialGrowth N.value :=
  N.stripGrowth_of_meromorphic hM hMg (stripGrowth_complexPairLFactor_denominator d d')
    (complexPairLFactor_denominator_ne_zero d d') hI

open RankinSelberg

/-- Finite-place Laurent normalizations obey the exponential bound with exponent zero. -/
theorem stripGrowth_laurentEval_spectralUnit {q : ℕ} (hq : 1 < q) (p : LaurentCoefficients) :
    HasStripExponentialGrowth (fun s => laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) s) p) := by
  intro a b
  obtain ⟨C, hC⟩ := exists_bound_laurentEval_spectralUnit hq p a b
  refine ⟨max C 0, 0, 0, le_max_right _ _, le_rfl, fun s hs ht _ => ?_⟩
  simpa only [zero_mul, Real.exp_zero, mul_one] using (hC s hs ht).trans (le_max_left _ _)

/-- A finite product of normalized factors with the strip growth bound, times
any fixed scalar, again has the bound. -/
def NormalizedProductStripGrowthStatement : Prop :=
  ∀ (ι : Type*) (S : Finset ι) (f : ι → ℂ → ℂ) (c : ℂ),
    (∀ i ∈ S, HasStripExponentialGrowth (f i)) →
      HasStripExponentialGrowth (fun s => c * ∏ i ∈ S, f i s)

theorem normalizedProductStripGrowth : NormalizedProductStripGrowthStatement := by
  intro ι S f c hf
  exact (HasStripExponentialGrowth.const c).mul (stripGrowth_finset_prod S f hf)

end Langlands.Global.RankinSelbergGlobal
