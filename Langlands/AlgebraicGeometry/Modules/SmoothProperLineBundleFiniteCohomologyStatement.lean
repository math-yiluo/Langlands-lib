import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Finite cohomology of line bundles on smooth proper field schemes -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- Actual line-bundle cohomology on a smooth proper scheme over a field
is finite dimensional in every degree and eventually zero. -/
def SmoothProperLineBundleFiniteCohomologyStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)),
    Smooth f → IsProper f →
      ∀ L : Picard.LineBundle X, DerivedSections.HasFiniteCohomology f L.obj

end Langlands.AlgebraicGeometry.Modules
