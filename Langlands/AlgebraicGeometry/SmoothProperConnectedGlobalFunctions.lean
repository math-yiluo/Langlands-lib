import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Relative global functions for smooth proper morphisms -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry

/-- For a smooth proper morphism with geometrically connected fibres, the
canonical map on sections is an isomorphism over every open of the base. -/
def SmoothProperConnectedGlobalFunctions : Prop :=
  ∀ (X S : _root_.AlgebraicGeometry.Scheme.{u}) (p : X ⟶ S),
    _root_.AlgebraicGeometry.Smooth p →
    _root_.AlgebraicGeometry.IsProper p →
    _root_.AlgebraicGeometry.GeometricallyConnected p →
    ∀ U : S.Opens, IsIso (p.app U)

end Langlands.AlgebraicGeometry
