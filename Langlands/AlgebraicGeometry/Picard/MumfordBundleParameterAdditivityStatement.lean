import Langlands.AlgebraicGeometry.Picard.MumfordBundle
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Parameter additivity of the actual relative Mumford family -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidalCategory

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The relative theorem-of-the-cube identity for the fixed parameter-first
Mumford family, as an equality of actual rigidified line-bundle classes. -/
def MumfordBundleParameterAdditivityStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left),
    let T : Over S := A.X ⊗ A.X
    let q : RigidifiedClasses A A.X :=
      RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
        (mumfordBundle A preservation L M evaluation)
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        μ[A.X] q =
      RigidifiedLineBundle.classesTensor preservation A.X.hom
        (unitSection A) (unitSection_comp A) T
        (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
          (unitSection_comp A) (CartesianMonoidalCategory.fst A.X A.X) q)
        (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
          (unitSection_comp A) (CartesianMonoidalCategory.snd A.X A.X) q)

end Langlands.AbelianScheme
