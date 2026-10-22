import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Filtration.ObjectDefinitions
import Mathlib.RingTheory.FiniteLength

/-! A finite detecting family of actual normalized Jacquet objects bounds length. -/

namespace Langlands.CuspidalSupport

open GeneralLinear
open scoped BigOperators

/-- Internal algebraic bridge motivated by BZ77 §2.14(2): bounded composition
lengths for a finite family of normalized Jacquet objects, together with
detection of every nonzero subquotient, imply finite length and the summed
composition bound for the ambient representation. This defines the proposition
without proving it. -/
def JacquetDetectingFamilyLengthTheorem.{uF, uV} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
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

end Langlands.CuspidalSupport
