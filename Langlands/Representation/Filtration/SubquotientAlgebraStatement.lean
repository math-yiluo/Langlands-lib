import Langlands.Representation.Classification.SupercuspidalSupport
import Mathlib.RingTheory.Artinian.Module

/-! Algebraic closure laws for actual smooth subquotient presentations. -/

namespace Langlands

universe uK uG uV

/-- Actual smooth subquotient presentations compose. -/
def SmoothSubquotientTransitivityTheorem : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Group G] [TopologicalSpace G]
    (A B C : SmoothRep.{uK, uG, uV} k G),
    SmoothRep.IsSubquotient C B → SmoothRep.IsSubquotient B A →
      SmoothRep.IsSubquotient C A

/-- The group-algebra Artinian condition passes to actual smooth subquotients. -/
def SmoothSubquotientArtinianTheorem : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Group G] [TopologicalSpace G]
    (A B : SmoothRep.{uK, uG, uV} k G),
    IsArtinian (MonoidAlgebra k G) A.representation.asModule →
      SmoothRep.IsSubquotient B A →
      IsArtinian (MonoidAlgebra k G) B.representation.asModule

/-- The two algebraic closure facts used to extract nested constituents. -/
def SmoothSubquotientAlgebraTheorem : Prop :=
  SmoothSubquotientTransitivityTheorem.{uK, uG, uV} ∧
  SmoothSubquotientArtinianTheorem.{uK, uG, uV}

end Langlands
