import Langlands.Representation.Category.Subquotients
import Mathlib.RingTheory.Artinian.Module

/-! A nonzero map into an Artinian representation gives a common constituent. -/

namespace Langlands

universe uK uG uV uW

/-- The image of a nonzero intertwiner into an Artinian representation contains
a simple submodule, which is an actual subquotient of both representations.
All four universes are independent. -/
def NonzeroHomCommonSubquotientTheorem : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Group G] [TopologicalSpace G]
    (A : SmoothRep.{uK, uG, uV} k G) (B : SmoothRep.{uK, uG, uW} k G),
    IsArtinian (MonoidAlgebra k G) B.representation.asModule →
    (∃ f : A.representation.IntertwiningMap B.representation, f ≠ 0) →
    ∃ (S : Subrepresentation A.representation)
      (Q : Subrepresentation (SmoothRep.subrepresentation A S).representation)
      (S' : Subrepresentation B.representation)
      (Q' : Subrepresentation (SmoothRep.subrepresentation B S').representation),
      (SmoothRep.subquotient A S Q).IsIrreducible ∧
      Nonempty ((SmoothRep.subquotient A S Q).representation.Equiv
        (SmoothRep.subquotient B S' Q').representation)

end Langlands
