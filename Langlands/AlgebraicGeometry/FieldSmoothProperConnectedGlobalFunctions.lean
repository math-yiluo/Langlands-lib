import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Global functions of smooth proper geometrically connected schemes over a field -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry

/-- The canonical map on global sections of a smooth proper geometrically connected
scheme over a field is an isomorphism. -/
def FieldSmoothProperConnectedGlobalFunctions : Prop :=
  ∀ (K : Type u) [Field K] (X : _root_.AlgebraicGeometry.Scheme.{u})
    (p : X ⟶ _root_.AlgebraicGeometry.Spec (CommRingCat.of K)),
    _root_.AlgebraicGeometry.Smooth p →
    _root_.AlgebraicGeometry.IsProper p →
    _root_.AlgebraicGeometry.GeometricallyConnected p →
    IsIso p.appTop

end Langlands.AlgebraicGeometry
