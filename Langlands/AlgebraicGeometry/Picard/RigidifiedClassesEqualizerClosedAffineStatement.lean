import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedStatement

/-! # The agreement locus over an affine base with identity parameter -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- For an abelian scheme over `Spec R` and two actual rigidified classes on
`Spec R ×_{Spec R} A`, there is a closed subscheme of `Spec R` through which a test
scheme factors exactly when the two classes agree after actual rigidified pullback. -/
def RigidifiedClassesEqualizerClosedAffineStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (A : AbelianScheme (Spec R))
    (q r : RigidifiedClasses A (Over.mk (𝟙 (Spec R)))),
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ Spec R), IsClosedImmersion ι ∧
      ∀ (T' : Over (Spec R)) (h : T' ⟶ Over.mk (𝟙 (Spec R))),
        (∃ g : T'.left ⟶ Z, g ≫ ι = h.left) ↔
          RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
              (unitSection_comp A) h q =
            RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
              (unitSection_comp A) h r

/-- The affine case is a literal specialization of the general statement. -/
example (h : RigidifiedClassesEqualizerClosedStatement.{u}) :
    RigidifiedClassesEqualizerClosedAffineStatement.{u} :=
  fun R A q r => h (Spec R) A (Over.mk (𝟙 (Spec R))) q r

end Langlands.AbelianScheme
