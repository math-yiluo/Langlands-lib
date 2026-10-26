import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Generic flatness for finite morphisms -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- The finite-morphism, locally Noetherian specialization of Stacks Project
Tag 052A: over an integral locally Noetherian target, a finite morphism becomes
flat after restriction to some nonempty target open.
This proposition is a statement target, not a proof of generic flatness. -/
def FiniteGenericFlatStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    IsIntegral Y → IsLocallyNoetherian Y → IsFinite f →
      ∃ U : Y.Opens, Set.Nonempty (U : Set Y) ∧ Flat (f ∣_ U)

end Langlands.AlgebraicGeometry
