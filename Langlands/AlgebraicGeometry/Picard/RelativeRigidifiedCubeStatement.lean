import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Relative cube detection for rigidified families on abelian schemes -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Over a quasi-separated base, two actual rigidified family classes for `A` over the
parameter product `B ×_S C` are equal once their pullbacks along the two unit axes
`(id, e_C)` and `(e_B, id)` agree. -/
def RelativeRigidifiedCubeStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A B C : AbelianScheme S)
    (q r : RigidifiedClasses A (B.X ⊗ C.X)),
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (CartesianMonoidalCategory.lift (𝟙 B.X) (1 : B.X ⟶ C.X)) q =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (CartesianMonoidalCategory.lift (𝟙 B.X) (1 : B.X ⟶ C.X)) r →
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (CartesianMonoidalCategory.lift (1 : C.X ⟶ B.X) (𝟙 C.X)) q =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
        (CartesianMonoidalCategory.lift (1 : C.X ⟶ B.X) (𝟙 C.X)) r →
    q = r

end Langlands.AbelianScheme
