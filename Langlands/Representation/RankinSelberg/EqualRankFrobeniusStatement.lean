import Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly

/-!
# Frobenius equivalence on actual row Schwartz functions vanishing at zero

The equivalence in JPSS (2.10.5)--(2.10.6) is stated for arbitrary smooth
representations. Its construction and proof remain separate obligations.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis GeneralLinear TrilinearReduction

universe uF uV uW

/-- The full twisted invariant trilinear space on actual row test functions
vanishing at zero is complex-linearly equivalent to the actual mirabolic
bilinear space with the modularly shifted covariance `|det p|^(1-s)`. -/
def EqualRankFrobeniusStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      IsSmooth ρ → IsSmooth σ →
      ∀ s : ℂ, Nonempty
        (invariantForms
          (S := (rowVanishingAtZero (F := F.Carrier) (n := n + 1)).toSubmodule)
          ρ σ (rowVanishingAtZero (F := F.Carrier) (n := n + 1)).toRepresentation
          (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) ≃ₗ[ℂ]
        InvariantBilinear.forms (ρ.comp (mirabolic n F.Carrier).subtype)
          (σ.comp (mirabolic n F.Carrier).subtype)
          (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (1 - s)))

end Langlands.RankinSelberg
