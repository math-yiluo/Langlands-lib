import Langlands.AlgebraicGeometry.Picard.StackAtlas
import Langlands.AlgebraicGeometry.Picard.RelativeAutomorphisms
import Langlands.AlgebraicGeometry.Picard.EtaleGroupoidClasses
import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-! # Smooth automorphisms and the etale sheaf of Picard classes: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A locally finite type smooth scheme presentation of the actual Picard
stack, with smooth automorphism schemes over every test, gives the ordinary
etale Picard class sheaf a representable diagonal and a surjective etale
scheme atlas locally of finite type over the base. -/
def SmoothAutomorphismEtaleAtlasStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S),
    (PicardGroupoid.relative f).IsStack (Scheme.fpqcTopology.over S) →
    PicardGroupoid.HasLocallyFiniteTypeSmoothSchemeAtlas f →
    PicardGroupoid.HasSmoothRelativeAutomorphismSchemes f →
      AlgebraicSpace.HasRepresentableDiagonal
        (RelativePicard.etaleClassSheafPresheaf f) ∧
      ∃ (U : Over S)
        (a : (AlgebraicSpace.schemeYoneda S).obj U ⟶
          RelativePicard.etaleClassSheafPresheaf f),
        AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
          LocallyOfFiniteType U.hom

end Langlands.AlgebraicGeometry.Picard
