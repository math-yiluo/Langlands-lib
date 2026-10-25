import Langlands.GroupScheme.GeneralLinear
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

universe u

namespace Langlands.GroupScheme.GeneralLinear

/-- The existing general linear group scheme is smooth over every commutative base ring. -/
def SmoothStatement : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}),
    AlgebraicGeometry.Smooth (groupScheme n R).X.hom

end Langlands.GroupScheme.GeneralLinear
