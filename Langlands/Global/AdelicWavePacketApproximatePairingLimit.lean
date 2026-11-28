import Langlands.Analysis.CompactSpectralPairingError
import Langlands.Global.AdelicWavePacketFourierPairing

/-! # Transferring the main-term limit to the pairing of full wave packets -/

noncomputable section

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace Langlands.Global

open Langlands.Analysis AdelicGroupPoints

local notation "Z[" n "]" => (Fin n → ℝ)
local notation "ζ[" n "]" => (volume : Measure Z[n])

/-- Compact spectral support, locally uniform fibre bounds and the central phase give the exact
Fourier pairing. Uniform errors then transfer a limit of the main-term integrals to it. -/
def WavePacketApproximatePairingLimitStatement : Prop :=
  ∀ {n n' u v m k k' : ℕ} {Q Q₁ H : Type*} [MeasurableSpace Q] [MeasurableSpace Q₁]
    (l : Filter H) (ν₁ : Measure Z[u]) (ν₂ : Measure Z[v]) (μG : Measure Q) (μ₁ : Measure Q₁)
    [IsLocallyFiniteMeasure ν₁] [IsLocallyFiniteMeasure ν₂] [SFinite μ₁]
    (Φ : (Z[m] × Q₁) ≃ᵐ Q) (A : (Z[u] × Z[m]) ≃ₗ[ℝ] Z[n])
    (A' : (Z[v] × Z[m]) ≃ₗ[ℝ] Z[n']),
    MeasurePreserving Φ (ζ[m].prod μ₁) μG →
    MeasurePreserving A (ν₁.prod ζ[m]) ζ[n] → MeasurePreserving A' (ν₂.prod ζ[m]) ζ[n'] →
    ∀ (C : Set Z[n]) (C' : Set Z[n']), IsCompact C → IsCompact C' →
    ∀ (c : Fin k → Z[n] → ℂ) (c' : Fin k' → Z[n'] → ℂ),
    (∀ j, Continuous (c j)) → (∀ j', Continuous (c' j')) →
    (∀ j, ∀ x ∉ C, c j x = 0) → (∀ j', ∀ x' ∉ C', c' j' x' = 0) →
    ∀ (F : H → Fin k → Z[n] → Q₁ → ℂ) (G : H → Fin k' → Z[n'] → Q₁ → ℂ)
      (E : H → Z[n] × Q → ℂ) (E' : H → Z[n'] × Q → ℂ)
      (M : H → Fin k → Fin k' → Z[n] × Z[n'] → ℂ) (L : ℂ),
    let S := equalFrequencyPair A A' ⁻¹' (C ×ˢ C')
    let η := ζ[m].prod (ν₁.prod ν₂)
    let f (t : H) (p : Z[n] × Q₁) : ℂ := ∑ j, c j p.1 * F t j p.1 p.2
    let g (t : H) (p : Z[n'] × Q₁) : ℂ := ∑ j', c' j' p.1 * G t j' p.1 p.2
    let approx (t : H) (p : Z[m] × (Z[u] × Z[v])) : ℂ :=
      let x := equalFrequencyPair A A' p
      ∑ j, ∑ j', c j x.1 * (starRingEnd ℂ) (c' j' x.2) * M t j j' x
    let packet (t : H) (q : Q) : ℂ := ∫ x, E t (x, q) ∂(spectralMeasure n)
    let packet' (t : H) (q : Q) : ℂ := ∫ x, E' t (x, q) ∂(spectralMeasure n')
    let scale : ℂ := (((2 * Real.pi) ^ m / ((2 * Real.pi) ^ n * (2 * Real.pi) ^ n') : ℝ) : ℂ)
    (∀ᶠ t in l,
      (∀ j, AEStronglyMeasurable (fun p => F t j p.1 p.2) ((ζ[n].restrict C).prod μ₁) ∧
        ∃ B : ℝ, ∀ x ∈ C, MemLp (F t j x) 2 μ₁ ∧ (∫ q, ‖F t j x q‖ ^ 2 ∂μ₁) ≤ B) ∧
      (∀ j', AEStronglyMeasurable (fun p => G t j' p.1 p.2) ((ζ[n'].restrict C').prod μ₁) ∧
        ∃ B : ℝ, ∀ x' ∈ C', MemLp (G t j' x') 2 μ₁ ∧ (∫ q, ‖G t j' x' q‖ ^ 2 ∂μ₁) ≤ B) ∧
      (∀ x y q, E t (x, Φ (y, q)) = coordinatePhase (A.symm x).2 y * f t (x, q)) ∧
      (∀ x y q, E' t (x, Φ (y, q)) = coordinatePhase (A'.symm x).2 y * g t (x, q)) ∧
      AEStronglyMeasurable (approx t) (η.restrict S)) →
    (∀ j j', ∃ ε : H → ℝ, Tendsto ε l (𝓝 0) ∧
      ∀ᶠ t in l, ∀ᵐ p ∂η.restrict S,
        let x := equalFrequencyPair A A' p
        ‖(∫ q, F t j x.1 q * (starRingEnd ℂ) (G t j' x.2 q) ∂μ₁) - M t j j' x‖ ≤ ε t) →
    Tendsto (fun t => scale * ∫ z, ∫ a, ∫ b, approx t (z, a, b) ∂ν₂ ∂ν₁ ∂ζ[m]) l (𝓝 L) →
    (∀ᶠ t in l, MemLp (packet t) 2 μG ∧ MemLp (packet' t) 2 μG) ∧
    Tendsto (fun t => ∫ q, packet t q * (starRingEnd ℂ) (packet' t q) ∂μG) l (𝓝 L)

/-- Use the fibre bounds in the Fourier pairing and integrate the vanishing errors. -/
theorem wavePacketApproximatePairingLimit : WavePacketApproximatePairingLimitStatement := by
  classical
  intro n n' u v m k k' Q Q₁ H _ _ l ν₁ ν₂ μG μ₁ _ _ _ Φ A A' hΦ hA hA' C C' hC hC'
    c c' hc hc' hc0 hc'0 F G E E' M L S η f g approx packet packet' scale hlarge herr hlim
  let pair (t : H) (p : Z[m] × (Z[u] × Z[v])) :=
    let x := equalFrequencyPair A A' p
    ∫ q, f t (x.1, q) * (starRingEnd ℂ) (g t (x.2, q)) ∂μ₁
  let I (p : Z[m] × (Z[u] × Z[v]) → ℂ) : ℂ := ∫ z, ∫ a, ∫ b, p (z, a, b) ∂ν₂ ∂ν₁ ∂ζ[m]
  have hexact : ∀ᶠ t in l,
      MemLp (packet t) 2 μG ∧ MemLp (packet' t) 2 μG ∧ Integrable (pair t) η ∧
        (∫ q, packet t q * (starRingEnd ℂ) (packet' t q) ∂μG) = scale * I (pair t) := by
    filter_upwards [hlarge] with t ⟨hF, hG, hE, hE', _⟩
    have hf := memLp_two_compact_weighted_sum hC hc (fun j => (hF j).1) (fun j => (hF j).2)
    have hg := memLp_two_compact_weighted_sum hC' hc' (fun j' => (hG j').1) (fun j' => (hG j').2)
    have hf0 : ∀ x ∉ C, ∀ q, f t (x, q) = 0 := by
      intro x hx q
      simp [f, hc0 _ _ hx]
    have hg0 : ∀ x ∉ C', ∀ q, g t (x, q) = 0 := by
      intro x hx q
      simp [g, hc'0 _ _ hx]
    exact wavePacketFourierPairing ν₁ ν₂ μG μ₁ Φ A A' hΦ hA hA' C C' (f t) (g t) (E t) (E' t)
      hC hC' hf hg hf0 hg0 hE hE'
  choose ε hε herror using herr
  have herrorAll : ∀ᶠ t in l, ∀ᵐ p ∂η.restrict S, ∀ j j',
      let x := equalFrequencyPair A A' p
      ‖(∫ q, F t j x.1 q * (starRingEnd ℂ) (G t j' x.2 q) ∂μ₁) - M t j j' x‖ ≤ ε j j' t := by
    have hh := eventually_all.mpr (fun j => eventually_all.mpr (herror j))
    exact hh.mono fun t ht => eventually_all.mpr (fun j => eventually_all.mpr (ht j))
  have hdiff : Tendsto (fun t => I (pair t) - I (approx t)) l (𝓝 0) := by
    refine (compactSpectralPairingError μ₁ ν₁ ν₂ l A A' C C' hC hC' c c' hc hc' hc0 hc'0
      F G M (fun t j j' => ε j j' t) ?_ hε).2
    filter_upwards [hlarge, hexact, herrorAll] with t ⟨hF, hG, _, _, hm⟩ ⟨_, _, hpair, _⟩ he
    refine ⟨hpair, hm, ?_, he⟩
    intro p hp
    let x := equalFrequencyPair A A' p
    have hx : x.1 ∈ C ∧ x.2 ∈ C' := hp
    exact ⟨fun j => ((hF j).2.choose_spec _ hx.1).1, fun j' => ((hG j').2.choose_spec _ hx.2).1⟩
  refine ⟨hexact.mono fun _ h => ⟨h.1, h.2.1⟩, ?_⟩
  have hlim' : Tendsto (fun t => scale * I (approx t)) l (𝓝 L) := hlim
  have hsum := hlim'.add (hdiff.const_mul scale)
  rw [mul_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hexact] with t ⟨_, _, _, ht⟩
  change scale * I (approx t) + scale * (I (pair t) - I (approx t)) = _
  rw [ht]
  ring

end Langlands.Global
