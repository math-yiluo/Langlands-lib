import Langlands.Analysis.CompactSpectralPacketPairing
import Langlands.Global.AdelicInducedInnerProduct

/-! # Fourier pairing with the spectral and quotient measure normalizations -/

noncomputable section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Langlands.Global

open Langlands.Analysis AdelicGroupPoints

local notation "Z[" n "]" => (Fin n → ℝ)
local notation "ζ[" n "]" => (volume : Measure (Fin n → ℝ))

private theorem integral_spectralMeasure {n : ℕ} (f : Z[n] → ℂ) :
    (∫ x, f x ∂(spectralMeasure n)) =
      Complex.ofReal (((2 * Real.pi : ℝ) ^ n)⁻¹) * ∫ x, f x ∂ζ[n] := by
  rw [spectralMeasure, integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity), inv_pow, Complex.real_smul]

/-- The chart of the quotient and the central transformation law turn the full truncated
spectral integrals into Plancherel packets with the exact spectral measure factors. -/
def WavePacketFourierPairingStatement : Prop :=
  ∀ {n n' u v m : ℕ} {Q Q₁ : Type*} [MeasurableSpace Q] [MeasurableSpace Q₁]
    (α : Measure Z[u]) (β : Measure Z[v]) (μ : Measure Q) (μ₁ : Measure Q₁)
    [IsLocallyFiniteMeasure α] [IsLocallyFiniteMeasure β] [SFinite μ₁]
    (H : (Z[m] × Q₁) ≃ᵐ Q) (A : (Z[u] × Z[m]) ≃ₗ[ℝ] Z[n])
    (A' : (Z[v] × Z[m]) ≃ₗ[ℝ] Z[n']),
    MeasurePreserving H (ζ[m].prod μ₁) μ →
    MeasurePreserving A (α.prod ζ[m]) ζ[n] → MeasurePreserving A' (β.prod ζ[m]) ζ[n'] →
    ∀ (C : Set Z[n]) (C' : Set Z[n']) (f : Z[n] × Q₁ → ℂ) (g : Z[n'] × Q₁ → ℂ)
      (F : Z[n] × Q → ℂ) (G : Z[n'] × Q → ℂ),
    IsCompact C → IsCompact C' →
    MemLp f 2 ((ζ[n].restrict C).prod μ₁) → MemLp g 2 ((ζ[n'].restrict C').prod μ₁) →
    (∀ x ∉ C, ∀ q, f (x, q) = 0) → (∀ x ∉ C', ∀ q, g (x, q) = 0) →
    (∀ x y q, F (x, H (y, q)) = coordinatePhase (A.symm x).2 y * f (x, q)) →
    (∀ x y q, G (x, H (y, q)) = coordinatePhase (A'.symm x).2 y * g (x, q)) →
    let packet (q : Q) := ∫ x, F (x, q) ∂(spectralMeasure n)
    let packet' (q : Q) := ∫ x, G (x, q) ∂(spectralMeasure n')
    let pairAt (z : Z[m]) (a : Z[u]) (b : Z[v]) :=
      ∫ q, f (A (a, z), q) * (starRingEnd ℂ) (g (A' (b, z), q)) ∂μ₁
    MemLp packet 2 μ ∧ MemLp packet' 2 μ ∧
    Integrable (fun p : Z[m] × (Z[u] × Z[v]) => pairAt p.1 p.2.1 p.2.2) (ζ[m].prod (α.prod β)) ∧
    (∫ q, packet q * (starRingEnd ℂ) (packet' q) ∂μ) =
      (((2 * Real.pi) ^ m / ((2 * Real.pi) ^ n * (2 * Real.pi) ^ n') : ℝ) : ℂ) *
        ∫ z, ∫ a, ∫ b, pairAt z a b ∂β ∂α ∂ζ[m]

/-- Transfer the compact Plancherel pairing through the quotient chart and rescale the two
spectral integrals. -/
theorem wavePacketFourierPairing : WavePacketFourierPairingStatement := by
  intro n n' u v m Q Q₁ _ _ α β μ μ₁ _ _ _ H A A' hH hA hA' C C' f g F G hC hC' hf hg
    hf0 hg0 hF hG packet packet' pairAt
  obtain ⟨hP, hP', hI, hEq⟩ := compactSpectralPacketPairing α β μ₁ A A' hA hA' C C' f g
    hC hC' hf hg hf0 hg0
  let d (j : ℕ) : ℂ := Complex.ofReal (((2 * Real.pi : ℝ) ^ j)⁻¹)
  have hpull (p : Z[m] × Q₁) : packet (H p) = d n * compactSpectralPacket A f p := by
    rcases p with ⟨y, q⟩
    change (∫ x, F (x, H (y, q)) ∂spectralMeasure n) = _
    rw [integral_spectralMeasure, compactSpectralPacket]
    simp only [hF, d]
  have hpull' (p : Z[m] × Q₁) : packet' (H p) = d n' * compactSpectralPacket A' g p := by
    rcases p with ⟨y, q⟩
    change (∫ x, G (x, H (y, q)) ∂spectralMeasure n') = _
    rw [integral_spectralMeasure, compactSpectralPacket]
    simp only [hG, d]
  have hback := hH.symm H
  refine ⟨?_, ?_, hI, ?_⟩
  · have hpullLp : MemLp (packet ∘ H) 2 (ζ[m].prod μ₁) := by
      rw [show packet ∘ H = d n • compactSpectralPacket A f from funext hpull]
      exact hP.const_smul (d n)
    simpa only [Function.comp_def, MeasurableEquiv.apply_symm_apply] using
      hpullLp.comp_measurePreserving hback
  · have hpullLp : MemLp (packet' ∘ H) 2 (ζ[m].prod μ₁) := by
      rw [show packet' ∘ H = d n' • compactSpectralPacket A' g from funext hpull']
      exact hP'.const_smul (d n')
    simpa only [Function.comp_def, MeasurableEquiv.apply_symm_apply] using
      hpullLp.comp_measurePreserving hback
  · rw [← hH.integral_comp H.measurableEmbedding]
    simp only [hpull, hpull', map_mul, d, Complex.conj_ofReal]
    conv_lhs =>
      enter [2, p]
      rw [mul_mul_mul_comm]
    rw [integral_const_mul, hEq, ← mul_assoc]
    congr 1
    push_cast
    ring

end Langlands.Global
