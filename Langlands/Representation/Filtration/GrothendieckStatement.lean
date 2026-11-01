import Langlands.Representation.Filtration.Definitions
import Langlands.Representation.Smooth.FiniteLengthGrothendieck

/-!
# Exact Grothendieck classes of naturally glued smooth functors

This proposition records the finite-filtration additivity needed to pass from
an actual geometric-lemma filtration to an equality in exact finite-length K0.
-/

open CategoryTheory
open scoped BigOperators

namespace Langlands.SmoothRep

universe uR uG uV uC vC

variable (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]

/-- An actual natural finite filtration gives the sum of its smooth graded
pieces in exact K0. Finite length of those pieces follows from the ambient
object; no irreducibility or finite-length premise on the pieces is added. -/
def FiltrationGrothendieckStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C]
    (F : C ⥤ SmoothRep.{uR, uG, uV} R G)
    (n : ℕ) (P : Fin n → C ⥤ SmoothRep.{uR, uG, uV} R G),
    IsGluedFrom (F ⋙ toRep) (fun i => P i ⋙ toRep) →
    ∀ (X : C) (hF : (F.obj X).HasFiniteLength),
      ∃ hP : ∀ i, ((P i).obj X).HasFiniteLength,
        FiniteLengthGrothendieckGroup.ofRepresentation (F.obj X) hF =
          ∑ i, FiniteLengthGrothendieckGroup.ofRepresentation ((P i).obj X) (hP i)

end Langlands.SmoothRep
