import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Twisted Burnside counting with possibly infinite fixed sets
-/

namespace Langlands

/-- The incidence count of elements `x` fixed by some `g • F` is the
order of the group times the number of orbits fixed by the induced map.
Only the acting group is required to be finite. -/
def TwistedBurnsideStatement.{uG, uX} : Prop :=
  ∀ (G : Type uG) [Group G] [Fintype G] (X : Type uX) [MulAction G X]
    (F : X → X) (hF : ∀ x y, MulAction.orbitRel G X x y → MulAction.orbitRel G X (F x) (F y)),
    (∑ g : G, ENat.card {x : X // g • F x = x}) =
      (Fintype.card G : ℕ∞) *
        ENat.card {o : MulAction.orbitRel.Quotient G X // Quotient.map' F hF o = o}

end Langlands
