import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding JacquetDetectingFamilyLengthTheorem
open Langlands.GeneralLinear
open scoped BigOperators
/-- Internal algebraic bridge motivated by BZ77 §2.14(2): bounded composition
lengths for a finite family of normalized Jacquet objects, together with
detection of every nonzero subquotient, imply finite length and the summed
composition bound for the ambient representation. This defines the proposition
without proving it. -/
def JacquetDetectingFamilyLengthTheorem.{uF, uV} : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (s : Finset (BlockShape n)) (b : BlockShape n → ℕ),
      (∀ C ∈ s,
        HasCompositionLengthAtMost
          (Rep.of ((T.normalizedJacquetFunctor C).obj A).representation) (b C)) →
      (∀ D : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
        SmoothRep.IsSubquotient D A → Nontrivial D →
          ∃ C ∈ s, Nontrivial ((T.normalizedJacquetFunctor C).obj D)) →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
          A.representation.asModule ∧
        HasCompositionLengthAtMost (Rep.of A.representation) (∑ C ∈ s, b C)

end Langlands.AllFieldBZ.CuspidalSupport
