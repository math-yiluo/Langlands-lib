import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Integrating the error in a compact spectral pairing -/

noncomputable section

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace Langlands.Analysis

local notation "Z[" n "]" => (Fin n → ℝ)
local notation "ζ[" n "]" => (volume : Measure (Fin n → ℝ))

/-- The two full spectral coordinates obtained from a common central coordinate and
independent relative coordinates. -/
def equalFrequencyPair {n n' u v m : ℕ}
    (A : (Z[u] × Z[m]) ≃ₗ[ℝ] Z[n]) (A' : (Z[v] × Z[m]) ≃ₗ[ℝ] Z[n'])
    (p : Z[m] × (Z[u] × Z[v])) : Z[n] × Z[n'] :=
  (A (p.2.1, p.1), A' (p.2.2, p.1))

/-- The two chart maps give a continuous map on the equal-frequency coordinates. -/
theorem continuous_equalFrequencyPair {n n' u v m : ℕ}
    (A : (Z[u] × Z[m]) ≃ₗ[ℝ] Z[n]) (A' : (Z[v] × Z[m]) ≃ₗ[ℝ] Z[n']) :
    Continuous (equalFrequencyPair A A') :=
  (A.toContinuousLinearEquiv.continuous.comp (continuous_snd.fst.prodMk continuous_fst)).prodMk
    (A'.toContinuousLinearEquiv.continuous.comp (continuous_snd.snd.prodMk continuous_fst))

/-- The set where both full coordinates belong to their compact spectral supports is compact
in the equal-frequency space. -/
theorem isCompact_equalFrequencySupport {n n' u v m : ℕ}
    (A : (Z[u] × Z[m]) ≃ₗ[ℝ] Z[n]) (A' : (Z[v] × Z[m]) ≃ₗ[ℝ] Z[n'])
    {C : Set Z[n]} {C' : Set Z[n']} (hC : IsCompact C) (hC' : IsCompact C') :
    IsCompact (equalFrequencyPair A A' ⁻¹' (C ×ˢ C')) := by
  let U := (Prod.fst ∘ A.symm) '' C
  let V := (Prod.fst ∘ A'.symm) '' C'
  let S := (Prod.snd ∘ A.symm) '' C
  have hA := A.symm.toContinuousLinearEquiv.continuous
  have hA' := A'.symm.toContinuousLinearEquiv.continuous
  have hU : IsCompact U := hC.image (continuous_fst.comp hA)
  have hV : IsCompact V := hC'.image (continuous_fst.comp hA')
  have hS : IsCompact S := hC.image (continuous_snd.comp hA)
  refine (hS.prod (hU.prod hV)).of_isClosed_subset
    ((hC.isClosed.prod hC'.isClosed).preimage (continuous_equalFrequencyPair A A')) ?_
  rintro ⟨z, a, b⟩ ⟨hx, hx'⟩
  exact ⟨⟨A (a, z), hx, by simp⟩, ⟨A (a, z), hx, by simp⟩, ⟨A' (b, z), hx', by simp⟩⟩

private theorem integral_weighted_pairing {Q : Type*} [MeasurableSpace Q] {μ : Measure Q}
    {k k' : ℕ} (w : Fin k → ℂ) (w' : Fin k' → ℂ) {f : Fin k → Q → ℂ} {g : Fin k' → Q → ℂ}
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : ∀ j', MemLp (g j') 2 μ) :
    (∫ q, (∑ j, w j * f j q) * (starRingEnd ℂ) (∑ j', w' j' * g j' q) ∂μ) =
      ∑ j, ∑ j', w j * (starRingEnd ℂ) (w' j') *
        (∫ q, f j q * (starRingEnd ℂ) (g j' q) ∂μ) := by
  have h (j : Fin k) (j' : Fin k') :
      Integrable (fun q => w j * (starRingEnd ℂ) (w' j') *
        (f j q * (starRingEnd ℂ) (g j' q))) μ :=
    ((hf j).integrable_mul (hg j').star).const_mul _
  have hmul (q : Q) :
      (∑ j, w j * f j q) * (starRingEnd ℂ) (∑ j', w' j' * g j' q) =
        ∑ j, ∑ j', w j * (starRingEnd ℂ) (w' j') * (f j q * (starRingEnd ℂ) (g j' q)) := by
    rw [map_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    ring
  have hsum (j : Fin k) :
      Integrable (fun q => ∑ j' ∈ (Finset.univ : Finset (Fin k')),
        w j * (starRingEnd ℂ) (w' j') * (f j q * (starRingEnd ℂ) (g j' q))) μ :=
    integrable_finsetSum _ fun j' _ => h j j'
  simp_rw [hmul]
  rw [integral_finsetSum (Finset.univ : Finset (Fin k)) (fun j _ => hsum j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum (Finset.univ : Finset (Fin k')) (fun j' _ => h j j')]
  exact Finset.sum_congr rfl fun j' _ => integral_const_mul _ _

private theorem integral_prod_three {X U V : Type*} [MeasurableSpace X] [MeasurableSpace U]
    [MeasurableSpace V] {μ : Measure X} {α : Measure U} {β : Measure V}
    [SFinite μ] [SFinite α] [SFinite β] {f : X × (U × V) → ℂ}
    (hf : Integrable f (μ.prod (α.prod β))) :
    (∫ p, f p ∂(μ.prod (α.prod β))) = ∫ z, ∫ a, ∫ b, f (z, a, b) ∂β ∂α ∂μ := by
  rw [integral_prod _ hf]
  exact integral_congr_ae (hf.prod_right_ae.mono fun _ hx => integral_prod _ hx)

/-- Compact support and uniform errors for the individual pairings give a vanishing error
between the two iterated spectral integrals. -/
def CompactSpectralPairingErrorStatement : Prop :=
  ∀ {n n' u v m k k' : ℕ} {Q H : Type*} [MeasurableSpace Q]
    (μ : Measure Q) (α : Measure Z[u]) (β : Measure Z[v])
    [IsLocallyFiniteMeasure α] [IsLocallyFiniteMeasure β] (l : Filter H)
    (A : (Z[u] × Z[m]) ≃ₗ[ℝ] Z[n]) (A' : (Z[v] × Z[m]) ≃ₗ[ℝ] Z[n'])
    (C : Set Z[n]) (C' : Set Z[n']) (_hC : IsCompact C) (_hC' : IsCompact C')
    (c : Fin k → Z[n] → ℂ) (c' : Fin k' → Z[n'] → ℂ),
    (∀ j, Continuous (c j)) → (∀ j', Continuous (c' j')) →
    (∀ j, ∀ x ∉ C, c j x = 0) → (∀ j', ∀ x' ∉ C', c' j' x' = 0) →
    ∀ (F : H → Fin k → Z[n] → Q → ℂ) (G : H → Fin k' → Z[n'] → Q → ℂ)
      (M : H → Fin k → Fin k' → Z[n] × Z[n'] → ℂ) (ε : H → Fin k → Fin k' → ℝ),
    let S := equalFrequencyPair A A' ⁻¹' (C ×ˢ C')
    let η := ζ[m].prod (α.prod β)
    let pair (t : H) (p : Z[m] × (Z[u] × Z[v])) : ℂ :=
      let x := equalFrequencyPair A A' p
      ∫ q, (∑ j, c j x.1 * F t j x.1 q) * (starRingEnd ℂ) (∑ j', c' j' x.2 * G t j' x.2 q) ∂μ
    let approx (t : H) (p : Z[m] × (Z[u] × Z[v])) : ℂ :=
      let x := equalFrequencyPair A A' p
      ∑ j, ∑ j', c j x.1 * (starRingEnd ℂ) (c' j' x.2) * M t j j' x
    (∀ᶠ t in l, Integrable (pair t) η ∧ AEStronglyMeasurable (approx t) (η.restrict S) ∧
      (∀ p ∈ S, (∀ j, MemLp (F t j (equalFrequencyPair A A' p).1) 2 μ) ∧
        (∀ j', MemLp (G t j' (equalFrequencyPair A A' p).2) 2 μ)) ∧
      ∀ᵐ p ∂η.restrict S, ∀ j j',
        let x := equalFrequencyPair A A' p
        ‖(∫ q, F t j x.1 q * (starRingEnd ℂ) (G t j' x.2 q) ∂μ) - M t j j' x‖ ≤ ε t j j') →
    (∀ j j', Tendsto (fun t => ε t j j') l (𝓝 0)) →
    (∀ᶠ t in l, Integrable (approx t) η) ∧
    Tendsto (fun t => (∫ z, ∫ a, ∫ b, pair t (z, a, b) ∂β ∂α ∂ζ[m]) -
      (∫ z, ∫ a, ∫ b, approx t (z, a, b) ∂β ∂α ∂ζ[m])) l (𝓝 0)

/-- Bound the weighted finite sum on the compact support, integrate the bound against
its finite restricted measure, and apply Fubini. -/
theorem compactSpectralPairingError : CompactSpectralPairingErrorStatement := by
  classical
  intro n n' u v m k k' Q H _ μ α β _ _ l A A' C C' hC hC' c c' hc hc' hc0 hc'0 F G M ε
    S η pair approx hlarge hε
  have hS : IsCompact S := isCompact_equalFrequencySupport A A' hC hC'
  let : IsFiniteMeasure (η.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  choose B hB using fun j => hC.exists_bound_of_continuousOn (hc j).continuousOn
  choose B' hB' using fun j' => hC'.exists_bound_of_continuousOn (hc' j').continuousOn
  let bound (t : H) : ℝ := ∑ j, ∑ j', (B j * B' j') * ε t j j'
  have hbound0 : Tendsto bound l (𝓝 0) := by
    have hterm (j : Fin k) (j' : Fin k') :
        Tendsto (fun t => (B j * B' j') * ε t j j') l (𝓝 0) := by
      simpa only [mul_zero] using (hε j j').const_mul (B j * B' j')
    simpa only [bound, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun j _ => tendsto_finsetSum Finset.univ fun j' _ => hterm j j')
  have hzero (t : H) (p : Z[m] × (Z[u] × Z[v])) (hp : p ∉ S) : pair t p = 0 ∧ approx t p = 0 := by
    let x := equalFrequencyPair A A' p
    have hx : ¬(x.1 ∈ C ∧ x.2 ∈ C') := hp
    rcases not_and_or.mp hx with hx | hx
    · simp [pair, approx, ← show x = equalFrequencyPair A A' p from rfl, hc0 _ _ hx]
    · simp [pair, approx, ← show x = equalFrequencyPair A A' p from rfl, hc'0 _ _ hx]
  have hestimate : ∀ᶠ t in l, Integrable (approx t) η ∧
      ‖(∫ z, ∫ a, ∫ b, pair t (z, a, b) ∂β ∂α ∂ζ[m]) -
        (∫ z, ∫ a, ∫ b, approx t (z, a, b) ∂β ∂α ∂ζ[m])‖ ≤ bound t * η.real S := by
    filter_upwards [hlarge] with t ⟨hpair, hm, hLp, he⟩
    have hlocal : ∀ᵐ p ∂η.restrict S, ‖pair t p - approx t p‖ ≤ bound t := by
      filter_upwards [ae_restrict_mem hS.measurableSet, he] with p hp hep
      let x := equalFrequencyPair A A' p
      have hx : x.1 ∈ C ∧ x.2 ∈ C' := hp
      let e (j : Fin k) (j' : Fin k') : ℂ :=
        (∫ q, F t j x.1 q * (starRingEnd ℂ) (G t j' x.2 q) ∂μ) - M t j j' x
      let w (j : Fin k) (j' : Fin k') : ℂ := c j x.1 * (starRingEnd ℂ) (c' j' x.2)
      have heq : pair t p - approx t p = ∑ j, ∑ j', w j j' * e j j' := by
        change (∫ q, (∑ j, c j x.1 * F t j x.1 q) *
          (starRingEnd ℂ) (∑ j', c' j' x.2 * G t j' x.2 q) ∂μ) -
          (∑ j, ∑ j', w j j' * M t j j' x) = _
        rw [integral_weighted_pairing _ _ (f := fun j => F t j x.1)
          (g := fun j' => G t j' x.2) (hLp p hp).1 (hLp p hp).2]
        simp only [w, e, ← Finset.sum_sub_distrib, ← mul_sub]
      rw [heq]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j' _ => ?_))
      have hweight : ‖w j j'‖ ≤ B j * B' j' := by
        change ‖c j x.1 * (starRingEnd ℂ) (c' j' x.2)‖ ≤ _
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hB j _ hx.1) (hB' j' _ hx.2) (norm_nonneg _)
          ((norm_nonneg _).trans (hB j _ hx.1))
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hep j j') (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hweight ((norm_nonneg (e j j')).trans (hep j j')))
    have hdiff : Integrable (fun p => pair t p - approx t p) (η.restrict S) :=
      (integrable_const (bound t)).mono' (hpair.restrict.aestronglyMeasurable.sub hm) hlocal
    have happroxOn : IntegrableOn (approx t) S η := by
      exact (hpair.restrict.sub hdiff).congr
        (Eventually.of_forall fun p => by simp only [Pi.sub_apply, sub_sub_cancel])
    have happrox := happroxOn.integrable_of_forall_notMem_eq_zero fun p hp => (hzero t p hp).2
    refine ⟨happrox, ?_⟩
    rw [← integral_prod_three hpair, ← integral_prod_three happrox, ← integral_sub hpair happrox]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (fun p hp => by
      rw [(hzero t p hp).1, (hzero t p hp).2, sub_self])]
    simpa only [measureReal_restrict_apply_univ] using norm_integral_le_of_norm_le_const hlocal
  refine ⟨hestimate.mono fun _ ht => ht.1, tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  have hlim : Tendsto (fun t => bound t * η.real S) l (𝓝 0) := by
    simpa only [zero_mul] using hbound0.mul_const (η.real S)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => norm_nonneg _) (hestimate.mono fun _ ht => ht.2)

end Langlands.Analysis
