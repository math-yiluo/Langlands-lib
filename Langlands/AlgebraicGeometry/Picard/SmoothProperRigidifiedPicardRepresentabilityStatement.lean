import Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
import Langlands.AlgebraicGeometry.Picard.RelativeGeometry
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Full rigidified Picard representability for smooth proper pointed schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Every smooth proper geometrically connected pointed scheme over a field has
a separated, locally finite type parameter scheme with an actual universal
rigidified line bundle, classifying families over every test scheme. -/
def SmoothProperRigidifiedPicardRepresentabilityStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Over (Spec (CommRingCat.of K))),
    Smooth X.hom → IsProper X.hom → GeometricallyConnected X.hom →
    ∀ (ε : Spec (CommRingCat.of K) ⟶ X.left) (section_eq : ε ≫ X.hom = 𝟙 _),
      ∃ (P : Over (Spec (CommRingCat.of K)))
        (L : RigidifiedLineBundle.relative X.hom ε section_eq P),
        IsSeparated P.hom ∧ LocallyOfFiniteType P.hom ∧
          RigidifiedLineBundle.IsUniversal X.hom ε section_eq L

end Langlands.AlgebraicGeometry.Picard
