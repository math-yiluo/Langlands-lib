import Langlands.GroupScheme.RelativeUnipotent.Basic
import Langlands.GroupScheme.RelativeLevi.Basic

/-! # Statement: finite vector-bundle series for supplied relative radicals -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over an arbitrary affine base, every supplied relative unipotent radical
of a parabolic in a reductive group has a finite vector-bundle normal series.
This is the finite-series consequence of Conrad (2014), Theorem 5.4.3,
using quasi-compactness of the affine base to bound the fibre dimensions.
Existence of the radical is not asserted. -/
def RelativeUnipotentRadicalFiltrationStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] (G P U : GroupScheme S)
    (i : P ⟶ G) (r : U ⟶ P),
    IsReductive G → IsRelativeParabolicSubgroup i →
    IsRelativeUnipotentRadical r →
      RelativeUnipotent.HasFiniteVectorBundleSeries U

end Langlands.GroupScheme
