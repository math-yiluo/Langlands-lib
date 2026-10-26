import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Topology.NoetherianSpace

/-! # Surjectivity of finite endomorphisms of irreducible Noetherian schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Every finite endomorphism of an irreducible scheme with Noetherian underlying
topological space is surjective on points. This defines a statement target. -/
def FiniteIrreducibleEndomorphismSurjectiveStatement : Prop :=
  ∀ (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] [IrreducibleSpace X]
    (f : X ⟶ X), IsFinite f → Surjective f

end Langlands.AlgebraicGeometry
