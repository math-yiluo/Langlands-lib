import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement

/-!
# All-field port of `Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Classification
open Langlands.Classification hiding IrreducibleProductFiniteLength
open Langlands.GeneralLinear
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData)

/-- Normalized upper parabolic induction of a finite family of arbitrary
irreducible smooth complex GL factors has finite group-module length.
The block shape includes positivity of each rank and their sum. -/
def IrreducibleProductFiniteLength : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (B : BlockShape n)
      (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
      (∀ i, (A i).IsIrreducible) →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
        ((T.normalizedProductInductionFunctor B).obj A).representation.asModule

end Langlands.AllFieldBZ.Classification
