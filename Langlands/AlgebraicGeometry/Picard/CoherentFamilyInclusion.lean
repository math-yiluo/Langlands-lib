import Langlands.AlgebraicGeometry.CoherentSheaves.Groupoid
import Langlands.AlgebraicGeometry.Picard.Groupoid
import Langlands.AlgebraicGeometry.Picard.LineBundleFinitePresentation
import Langlands.AlgebraicGeometry.Picard.LineBundleStalkFlatness

/-! # Inclusion of actual line bundles into flat finitely presented families -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open CoherentSheaves

variable {X Y S : Scheme.{u}}

/-- A line bundle on a flat scheme over the base is an actual flat locally
finitely presented family over that base. -/
def LineBundle.toFamily (p : X ⟶ Y) [Flat p] :
    LineBundle X ⥤ Family p :=
  ObjectProperty.ιOfLE (fun _ hM => ⟨hM.isFinitePresentation, hM.isFlatOver p⟩)

instance (p : X ⟶ Y) [Flat p] : (LineBundle.toFamily p).Full := by
  dsimp only [LineBundle.toFamily]
  infer_instance

instance (p : X ⟶ Y) [Flat p] : (LineBundle.toFamily p).Faithful := by
  dsimp only [LineBundle.toFamily]
  infer_instance

/-- The inclusion retains the actual underlying module sheaves and maps. -/
def LineBundle.toFamilyForgetIso (p : X ⟶ Y) [Flat p] :
    toFamily p ⋙ Family.forget p ≅ forget X :=
  Iso.refl _

namespace PicardGroupoid

/-- Include the actual Picard groupoid into the core of flat locally finitely
presented modules over a flat structure morphism. -/
def toFamily (p : X ⟶ Y) [Flat p] :
    PicardGroupoid X ⥤ Core (Family p) :=
  (LineBundle.toFamily p).core

/-- Every actual module isomorphism between the image line bundles lifts
uniquely to their original Picard-groupoid arrow. -/
def toFamilyFullyFaithful (p : X ⟶ Y) [Flat p] :
    (toFamily p).FullyFaithful where
  preimage a := ⟨ObjectProperty.isoMk _
    ((Family.forget p).mapIso a.iso)⟩
  map_preimage a := by
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    rfl
  preimage_map a := by
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    rfl

instance (p : X ⟶ Y) [Flat p] : (toFamily p).Full :=
  (toFamilyFullyFaithful p).full

instance (p : X ⟶ Y) [Flat p] : (toFamily p).Faithful :=
  (toFamilyFullyFaithful p).faithful

/-- On every actual test scheme, the original Picard groupoid includes into
the coherent-family groupoid on the same actual fibre product. -/
def relativeToFamily (f : X ⟶ S) [Flat f] (T : Over S) :
    PicardGroupoid ((relativeSpace f).obj T) ⥤ FamilyGroupoid f T := by
  letI : Flat ((relativeProjection f).app T) := by
    change Flat (CategoryTheory.Limits.pullback.fst T.hom f)
    infer_instance
  exact toFamily ((relativeProjection f).app T)

/-- The inclusion is fully faithful on every test scheme in the full slice. -/
def relativeToFamilyFullyFaithful (f : X ⟶ S) [Flat f] (T : Over S) :
    (relativeToFamily f T).FullyFaithful := by
  letI : Flat ((relativeProjection f).app T) := by
    change Flat (CategoryTheory.Limits.pullback.fst T.hom f)
    infer_instance
  exact toFamilyFullyFaithful ((relativeProjection f).app T)

instance (f : X ⟶ S) [Flat f] (T : Over S) : (relativeToFamily f T).Full :=
  (relativeToFamilyFullyFaithful f T).full

instance (f : X ⟶ S) [Flat f] (T : Over S) : (relativeToFamily f T).Faithful :=
  (relativeToFamilyFullyFaithful f T).faithful

@[simp]
lemma relativeToFamily_obj_module (f : X ⟶ S) [Flat f] (T : Over S)
    (L : PicardGroupoid ((relativeSpace f).obj T)) :
    ((relativeToFamily f T).obj L).of.obj = L.of.obj := rfl

@[simp]
lemma relativeToFamily_map_module (f : X ⟶ S) [Flat f] (T : Over S)
    {L M : PicardGroupoid ((relativeSpace f).obj T)} (a : L ⟶ M) :
    (FamilyGroupoid.forget f T).map ((relativeToFamily f T).map a) =
      a.iso.hom.hom := rfl

end PicardGroupoid

end Langlands.AlgebraicGeometry.Picard
