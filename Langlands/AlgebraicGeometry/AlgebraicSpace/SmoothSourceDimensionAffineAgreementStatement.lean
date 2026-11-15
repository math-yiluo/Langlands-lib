import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceAnalyticStructure

/-! # Affine-space normalization of the assembled varying-dimension structure -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology

/-- For an admissible pure-dimensional family over a henselian field, the
assembled varying-dimension structure satisfies the affine-space normalization:
on every polynomial affine space, the actual coordinate map is a bijection that
is analytic in both directions for the assembled atlas. -/
def SmoothSourceDimensionAffineAgreementStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (hK : IsHenselianValuedField K)
    (σ : AnalyticPointStructure K), σ.IsAdmissible →
      (σ.dimensionStructure hK).AgreesWithAffineSpace

end Langlands.AlgebraicGeometry.AlgebraicSpace
