import Langlands.AllFieldBZ.Representation.Derivative.Iteration
import Langlands.Representation.Classification.SupercuspidalDerivativesStatement

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalDerivativesStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalDerivativesStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Classification
open Langlands.Classification hiding SupercuspidalDerivatives
universe uF uW

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

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

end Langlands.AllFieldBZ.Classification
