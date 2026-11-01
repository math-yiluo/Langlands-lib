import Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycle
import Langlands.Group.GL.MirabolicMixedOrbitCoverageProof

/-!
# The positive-rank `Φ⁻` sequence of BZ77 Proposition 4.13(c)

For `τ` on `P_(r+2)` and `ρ` on `GL_(k+1)`, the sequence
`0 → (Φ⁻τ) × ρ → Φ⁻(τ × ρ) → (Ψ⁻τ) × (ρ|P) → 0` is natural and short exact. The two
orbits of the plus subgroup on the right mixed inducing subgroup, cycle first, are the
published coverage; the open (cycle) piece is `(Φ⁻τ) × ρ` and the closed (identity)
piece is `(Ψ⁻τ) × (ρ|P)`.
-/

noncomputable section

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- BZ77 4.13(c), `Φ⁻` clause at positive source rank: the natural sequence
`0 → (Φ⁻τ) × ρ → Φ⁻(τ × ρ) → (Ψ⁻τ) × (ρ|P) → 0` is short exact. -/
theorem rightPhiShortExact (T : F.TopologicalData) : RightPhiShortExact.{uF, uV} F T := by
  let := T.topology
  intro ψ k r
  let := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  obtain ⟨s, hs⟩ := (mirabolicMixedOrbitCoverage F T).2 k r
  obtain ⟨E₀⟩ := rightPhiCyclePiece_iso.{uF, uV} T ψ k r
  obtain ⟨E₁⟩ := rightPhiIdentityPiece_iso.{uF, uV} T ψ k r
  exact rightPhiShortExact_of_pieces T ψ k r s hs E₀ E₁

end Langlands.Derivative.MirabolicProductMinus
