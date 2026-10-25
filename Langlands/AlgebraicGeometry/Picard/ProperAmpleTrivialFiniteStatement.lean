import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Finiteness of a proper field scheme with an ample trivial line bundle -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A proper scheme over any field is finite over that field if it has an ample
line bundle isomorphic, as a module sheaf, to its structure sheaf. -/
def ProperAmpleTrivialFiniteStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) (L : LineBundle X),
    IsProper f → L.IsAmple →
    Nonempty (L.obj ≅ SheafOfModules.unit X.ringCatSheaf) → IsFinite f

end Langlands.AlgebraicGeometry.Picard
