import Langlands.GroupScheme.Torus.GaloisNorm
import Langlands.GroupScheme.Torus.Split
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Statement: smoothness of the finite-Galois torus norm -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual algebraic norm is smooth when the finite Galois extension
splits the base-changed group as a torus. -/
def GaloisNormSmoothnessStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
    [IsAffine (GaloisPointComparison.baseChanged k L T.toGrp).X.left]
    [LocallyOfFiniteType (GaloisPointComparison.baseChanged k L T.toGrp).X.hom],
    IsSplitTorus (GaloisPointComparison.baseChanged k L T.toGrp) →
      Smooth (GaloisNorm.norm k L T).hom.hom.left

end Langlands.GroupScheme
