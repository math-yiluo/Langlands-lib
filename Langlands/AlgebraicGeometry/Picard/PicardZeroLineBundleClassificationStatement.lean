import Langlands.AlgebraicGeometry.Picard.DualScheme
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor

/-! # Classification of geometrically Picard-zero line bundles up to a base twist -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Every line bundle on `T ×_S A` that is Picard-zero on geometric fibres is the
pullback of the chosen Poincaré bundle along some parameter map, tensored with the
pullback from `T` of its own restriction along the unit section. -/
def PicardZeroLineBundleClassificationStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A) (T : Over S)
    (N : LineBundle ((relativeSpace A.X.hom).obj T)),
    IsGeometricallyPicardZero ((baseChange T.hom).obj A)
        ((LineBundle.pullback (relativeSpaceSymmetry A.X.hom T).inv).obj N) →
      ∃ φ : T ⟶ dualScheme A hA,
        Nonempty (N ≅ LineBundle.tensor preservation
          ((RigidifiedLineBundle.forget _).obj
            ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
              (unitSection_comp A) φ).obj (poincareFamily A hA)))
          ((LineBundle.pullback ((relativeProjection A.X.hom).app T)).obj
            ((LineBundle.pullback ((relativeSection A.X.hom (unitSection A)
              (unitSection_comp A)).app T)).obj N)))

end Langlands.AbelianScheme
