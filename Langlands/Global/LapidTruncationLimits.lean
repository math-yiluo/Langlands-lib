import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Passing from truncated pairings to full pairings

This is the measure-theoretic step of Lapid 2011, Lemma 9 and §8. It takes almost-everywhere
convergence of the truncations and agreement with orthogonal projections on `L²` as hypotheses.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace

namespace Langlands.Global

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
  {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]

-- Mathlib conjugates the first entry, whereas the adelic formulas conjugate the second.
private theorem inner_toLp_eq_pairing {f k : X → ℂ} (hf : MemLp f 2 μ) (hk : MemLp k 2 μ) :
    inner ℂ (hk.toLp k) (hf.toLp f) = ∫ x, f x * (starRingEnd ℂ) (k x) ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hk.coeFn_toLp] with x hx hy
  rw [RCLike.inner_apply, hx, hy]

/-- Fatou's lemma in the form used for Lapid's `L²` test: an eventual bound on the real
self-pairings of the approximants suffices. The approximants must be square integrable (the
Bochner integral is defined to be zero for a nonintegrable integrand). -/
theorem memLp_two_of_ae_tendsto_of_bounded_selfPairings {f : X → ℂ} {g : ι → X → ℂ}
    (hf : AEStronglyMeasurable f μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => g i x) l (𝓝 (f x)))
    (hbound : ∃ C : ℝ, ∀ᶠ i in l, (∫ x, g i x * (starRingEnd ℂ) (g i x) ∂μ).re ≤ C) :
    MemLp f 2 μ := by
  obtain ⟨C, hC⟩ := hbound
  have hB : ∀ᶠ i in l, eLpNorm (g i) 2 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
    filter_upwards [hC] with i hi
    rw [← Lp.enorm_toLp (hg i), ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    apply Real.le_sqrt_of_sq_le
    simpa only [norm_sq_eq_re_inner (𝕜 := ℂ), inner_toLp_eq_pairing,
      RCLike.re_eq_complex_re] using hi
  exact (Lp.eLpNorm_le_of_ae_tendsto hB (fun i => (hg i).aestronglyMeasurable)
    hf hlim).trans_lt ENNReal.ofReal_lt_top

omit [l.NeBot] in
/-- Almost-everywhere convergence and eventual agreement with orthogonal projections imply
strong `L²` convergence, when the limit is already in `L²`. -/
theorem tendsto_toLp_of_ae_tendsto_of_starProjection {f : X → ℂ} {g : ι → X → ℂ}
    (hf : MemLp f 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => g i x) l (𝓝 (f x)))
    (P : ι → (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) (hP : ∀ᶠ i in l, IsStarProjection (P i))
    (hagree : ∀ᶠ i in l, (hg i).toLp (g i) = P i (hf.toLp f)) :
    Tendsto (fun i => (hg i).toLp (g i)) l (𝓝 (hf.toLp f)) := by
  let a := hf.toLp f
  let b i := (hg i).toLp (g i)
  have hpyth : ∀ᶠ i in l, ‖a‖ ^ 2 = ‖b i‖ ^ 2 + ‖b i - a‖ ^ 2 := by
    filter_upwards [hP, hagree] with i hi hbi
    obtain ⟨S, hS, hS_eq⟩ := isStarProjection_iff_eq_starProjection.mp hi
    let := hS
    change b i = P i a at hbi
    rw [hbi, hS_eq, norm_sub_rev (S.starProjection a) a]
    simpa [Submodule.starProjection_orthogonal, sub_apply] using
      (Submodule.norm_sq_eq_add_norm_sq_starProjection a S)
  have hu : ∀ᶠ i in l, eLpNorm (g i) 2 μ ≤ eLpNorm f 2 μ := by
    filter_upwards [hpyth] with i hi
    rw [← Lp.enorm_toLp (hg i), ← Lp.enorm_toLp hf, ← ofReal_norm, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    change ‖b i‖ ≤ ‖a‖
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    linarith [sq_nonneg ‖b i - a‖]
  have he : Tendsto (fun i => eLpNorm (g i) 2 μ) l (𝓝 (eLpNorm f 2 μ)) := by
    refine tendsto_order.2 ⟨?_, fun C hC => hu.mono fun i hi => hi.trans_lt hC⟩
    intro C hC
    by_contra h
    have hfreq : ∃ᶠ i in l, eLpNorm (g i) 2 μ ≤ C :=
      fun he => h (he.mono fun _ hi => lt_of_not_ge hi)
    let s : Set ι := {i | eLpNorm (g i) 2 μ ≤ C}
    let : NeBot (l ⊓ 𝓟 s) := frequently_iff_neBot.mp hfreq
    have hb : ∀ᶠ i in l ⊓ 𝓟 s, eLpNorm (g i) 2 μ ≤ C :=
      eventually_inf_principal.2 (Eventually.of_forall fun _ hi => hi)
    exact hC.not_ge (Lp.eLpNorm_le_of_ae_tendsto hb (fun i => (hg i).aestronglyMeasurable)
      hf.aestronglyMeasurable (hlim.mono fun _ hx => hx.mono_left inf_le_left))
  have hn : Tendsto (fun i => ‖b i‖) l (𝓝 ‖a‖) := by
    simpa only [a, b, Lp.norm_toLp, Function.comp_def] using
      (ENNReal.continuousAt_toReal hf.eLpNorm_ne_top).tendsto.comp he
  have hsq : Tendsto (fun i => ‖b i - a‖ ^ 2) l (𝓝 0) := by
    have hr := (tendsto_const_nhds (x := ‖a‖ ^ 2) (f := l)).sub (hn.pow 2)
    rw [sub_self] at hr
    refine hr.congr' (hpyth.mono fun i hi => ?_)
    change ‖a‖ ^ 2 - ‖b i‖ ^ 2 = ‖b i - a‖ ^ 2
    linarith
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

/-- The conditional endgame of Lapid 2011, §8, for two functions on a measure space.
Bounded diagonal pairings of the truncations give square integrability; the limit of the
mixed truncated pairing gives the untruncated pairing. No pairing of an untruncated
function with a truncation is needed before square integrability is established. -/
theorem pairing_eq_of_truncation_limits {f f' : X → ℂ} {g g' : ι → X → ℂ} {z : ℂ}
    (hf : AEStronglyMeasurable f μ) (hf' : AEStronglyMeasurable f' μ)
    (hg : ∀ i, MemLp (g i) 2 μ) (hg' : ∀ i, MemLp (g' i) 2 μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => g i x) l (𝓝 (f x)))
    (hlim' : ∀ᵐ x ∂μ, Tendsto (fun i => g' i x) l (𝓝 (f' x)))
    (hbound : ∃ C : ℝ, ∀ᶠ i in l, (∫ x, g i x * (starRingEnd ℂ) (g i x) ∂μ).re ≤ C)
    (hbound' : ∃ C : ℝ, ∀ᶠ i in l, (∫ x, g' i x * (starRingEnd ℂ) (g' i x) ∂μ).re ≤ C)
    (P : ι → (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) (hP : ∀ᶠ i in l, IsStarProjection (P i))
    (hagree : ∀ h : MemLp f 2 μ, ∀ᶠ i in l, (hg i).toLp (g i) = P i (h.toLp f))
    (hagree' : ∀ h : MemLp f' 2 μ, ∀ᶠ i in l, (hg' i).toLp (g' i) = P i (h.toLp f'))
    (hz : Tendsto (fun i => ∫ x, g i x * (starRingEnd ℂ) (g' i x) ∂μ) l (𝓝 z)) :
    MemLp f 2 μ ∧ MemLp f' 2 μ ∧ ∫ x, f x * (starRingEnd ℂ) (f' x) ∂μ = z := by
  have h₂ := memLp_two_of_ae_tendsto_of_bounded_selfPairings hf hg hlim hbound
  have h₂' := memLp_two_of_ae_tendsto_of_bounded_selfPairings hf' hg' hlim' hbound'
  have ht := tendsto_toLp_of_ae_tendsto_of_starProjection h₂ hg hlim P hP (hagree h₂)
  have ht' := tendsto_toLp_of_ae_tendsto_of_starProjection h₂' hg' hlim' P hP (hagree' h₂')
  refine ⟨h₂, h₂', tendsto_nhds_unique ?_ hz⟩
  simpa only [inner_toLp_eq_pairing] using ht'.inner (𝕜 := ℂ) ht

/-- The measure-theoretic reduction of Lapid 2011, Lemma 9 and §8, with the convergence,
projection, and pairing-limit inputs isolated. -/
def TruncationPairingLimitStatement : Prop :=
  ∀ {Y J : Type*} [MeasurableSpace Y] {ν : Measure Y} {L : Filter J}
    [L.NeBot] [L.IsCountablyGenerated] {f f' : Y → ℂ} {g g' : J → Y → ℂ} {z : ℂ},
    AEStronglyMeasurable f ν → AEStronglyMeasurable f' ν →
    ∀ (hg : ∀ j, MemLp (g j) 2 ν) (hg' : ∀ j, MemLp (g' j) 2 ν),
    (∀ᵐ y ∂ν, Tendsto (fun j => g j y) L (𝓝 (f y))) →
    (∀ᵐ y ∂ν, Tendsto (fun j => g' j y) L (𝓝 (f' y))) →
    (∃ C : ℝ, ∀ᶠ j in L, (∫ y, g j y * (starRingEnd ℂ) (g j y) ∂ν).re ≤ C) →
    (∃ C : ℝ, ∀ᶠ j in L, (∫ y, g' j y * (starRingEnd ℂ) (g' j y) ∂ν).re ≤ C) →
    ∀ Q : J → (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν),
    (∀ᶠ j in L, IsStarProjection (Q j)) →
    (∀ h : MemLp f 2 ν, ∀ᶠ j in L, (hg j).toLp (g j) = Q j (h.toLp f)) →
    (∀ h : MemLp f' 2 ν, ∀ᶠ j in L, (hg' j).toLp (g' j) = Q j (h.toLp f')) →
    Tendsto (fun j => ∫ y, g j y * (starRingEnd ℂ) (g' j y) ∂ν) L (𝓝 z) →
    MemLp f 2 ν ∧ MemLp f' 2 ν ∧ ∫ y, f y * (starRingEnd ℂ) (f' y) ∂ν = z

theorem truncationPairingLimit : TruncationPairingLimitStatement :=
  pairing_eq_of_truncation_limits

end Langlands.Global
