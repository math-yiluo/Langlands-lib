import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The locus where two rigidified classes agree is closed -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- For two actual rigidified isomorphism classes on `T ×_S A`, there is a closed subscheme
`Z` of `T` such that a test morphism `T' ⟶ T` over `S` factors through `Z` exactly when the
two classes become equal after actual rigidified pullback to `T'`. -/
def RigidifiedClassesEqualizerClosedStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (T : Over S) (q r : RigidifiedClasses A T),
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ T.left), IsClosedImmersion ι ∧
      ∀ (T' : Over S) (h : T' ⟶ T), (∃ g : T'.left ⟶ Z, g ≫ ι = h.left) ↔
        RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
            (unitSection_comp A) h q =
          RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
            (unitSection_comp A) h r

end Langlands.AbelianScheme
