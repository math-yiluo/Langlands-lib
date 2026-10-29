import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Derivative.Iteration
import Langlands.HarmonicAnalysis.Basic

/-!
# Derivatives of irreducible supercuspidal representations

The BZ77 §4.4 Gelfand–Kazhdan statement for the actual
`Derivative.generalLinearDerivative T ψ N k hk`, independently of segment
socles. This proposition is unproved here.
-/

namespace Langlands.Classification

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- (a) BZ77 §4.4 (Gelfand–Kazhdan): an irreducible supercuspidal representation
of `GL_(n+1)` has vanishing derivatives of every order strictly between `0` and
`n + 1`, and a one-dimensional top derivative. -/
def SupercuspidalDerivatives : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear (n + 1) F.Carrier)),
    A.IsIrreducible → GeneralLinear.IsSupercuspidal A.representation →
      (∀ (k : ℕ) (hk : k ≤ n + 1), 0 < k → k < n + 1 →
        Subsingleton
          ((Derivative.generalLinearDerivative.{uF, uW} T ψ (n + 1) k hk).obj A)) ∧
      Module.finrank ℂ
        ((Derivative.generalLinearDerivative.{uF, uW} T ψ (n + 1) (n + 1) le_rfl).obj A) = 1

end Langlands.Classification
