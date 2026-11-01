import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Connected schemes over an algebraically closed field -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

universe u

/-- Connectedness of a scheme locally of finite type over an algebraically closed
field implies geometric connectedness of its structure morphism. -/
def AlgClosedConnectedStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] [ConnectedSpace X],
    GeometricallyConnected f

end Langlands.AlgebraicGeometry
