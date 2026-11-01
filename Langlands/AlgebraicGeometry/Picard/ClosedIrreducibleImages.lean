import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-! # Closed images of closed irreducible subsets -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- The image of every closed irreducible subset of the source is closed.
This is the topological condition in the last assertion of EGA IV 18.10.19. -/
def ClosedIrreducibleImages {X S : Scheme.{u}} (p : X ⟶ S) : Prop :=
  ∀ Z : Set X, IsClosed Z → IsIrreducible Z → IsClosed (p '' Z)

/-- A closed map has closed images of closed irreducible subsets. -/
theorem closedIrreducibleImages_of_isClosedMap {X S : Scheme.{u}} (p : X ⟶ S)
    (hp : IsClosedMap p) : ClosedIrreducibleImages p := by
  intro Z hZ _
  exact hp Z hZ

/-- Universal closedness implies the EGA closed-image condition on this base. -/
theorem closedIrreducibleImages_of_universallyClosed {X S : Scheme.{u}}
    (p : X ⟶ S) [UniversallyClosed p] : ClosedIrreducibleImages p :=
  closedIrreducibleImages_of_isClosedMap p p.isClosedMap

end Langlands.AlgebraicGeometry
