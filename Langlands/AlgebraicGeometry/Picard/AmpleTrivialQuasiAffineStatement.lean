import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Quasi-affineness from an ample trivial line bundle -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A scheme with an ample line bundle isomorphic to its structure sheaf is quasi-affine. -/
def AmpleTrivialQuasiAffineStatement : Prop :=
  ∀ (X : Scheme.{u}) (L : LineBundle X),
    L.IsAmple →
      Nonempty (L.obj ≅ SheafOfModules.unit X.ringCatSheaf) →
        Scheme.IsQuasiAffine X

end Langlands.AlgebraicGeometry.Picard
