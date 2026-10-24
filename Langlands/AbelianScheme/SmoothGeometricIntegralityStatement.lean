import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Geometric integrality of smooth geometrically connected schemes over fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A smooth geometrically connected scheme over any field is geometrically integral. -/
def SmoothGeometricIntegrality : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K)),
    Smooth p → GeometricallyConnected p → GeometricallyIntegral p

end Langlands.AbelianScheme
