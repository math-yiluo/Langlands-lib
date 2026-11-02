import Langlands.AlgebraicGeometry.Picard.StackAtlas
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Smooth scheme atlases of the Picard stack over a field: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For a proper scheme over any field, the actual relative line-bundle
groupoid has a smooth surjective scheme atlas locally of finite type over
the field. Its point fibres are represented by schemes on the full slice. -/
def FieldPicardStackAtlasStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))),
    IsProper X.hom →
      PicardGroupoid.HasLocallyFiniteTypeSmoothSchemeAtlas X.hom

end Langlands.AlgebraicGeometry.Picard
