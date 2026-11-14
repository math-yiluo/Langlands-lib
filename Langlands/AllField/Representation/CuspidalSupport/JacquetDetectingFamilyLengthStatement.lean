import Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement
import Langlands.AllField.Representation.Jacquet.ParabolicSupplement
/-! A finite detecting family of actual normalized Jacquet objects bounds length. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding JacquetDetectingFamilyLengthTheorem
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open scoped BigOperators

/-- Internal algebraic bridge motivated by BZ77 §2.14(2): bounded composition
lengths for a finite family of normalized Jacquet objects, together with
detection of every nonzero subquotient, imply finite length and the summed
composition bound for the ambient representation. This defines the proposition
without proving it. -/
def JacquetDetectingFamilyLengthTheorem.{uF, uV} : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ),
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F))
      (s : Finset (BlockShape n)) (b : BlockShape n → ℕ),
      (∀ C ∈ s,
        HasCompositionLengthAtMost
          (Rep.of ((T.normalizedJacquetFunctor C).obj A).representation) (b C)) →
      (∀ D : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F),
        SmoothRep.IsSubquotient D A → Nontrivial D →
          ∃ C ∈ s, Nontrivial ((T.normalizedJacquetFunctor C).obj D)) →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F))
          A.representation.asModule ∧
        HasCompositionLengthAtMost (Rep.of A.representation) (∑ C ∈ s, b C)

end Langlands.AllField.CuspidalSupport
