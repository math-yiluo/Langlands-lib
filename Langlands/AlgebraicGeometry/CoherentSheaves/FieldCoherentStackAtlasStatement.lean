import Langlands.AlgebraicGeometry.CoherentSheaves.Pullback
import Langlands.AlgebraicGeometry.Stacks.SchemeAtlas
import Langlands.CategoryTheory.Sites.PseudofunctorHomLift
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Smooth scheme atlases of the actual coherent-family stack over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.CoherentSheaves

/-- For every proper scheme over a field, the actual groupoid of flat finitely
presented module families has a smooth surjective scheme atlas locally of
finite type over the field, with scheme-represented fibres on the full slice. -/
def FieldCoherentStackAtlasStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))),
    IsProper X.hom →
      Stacks.HasLocallyFiniteTypeSmoothSchemeAtlas
        (Langlands.CategoryTheory.PseudofunctorHomLift.homLift.{u + 1}
          (FamilyGroupoid.pseudofunctor X.hom))

end Langlands.AlgebraicGeometry.CoherentSheaves
