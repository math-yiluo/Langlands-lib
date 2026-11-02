import Langlands.AlgebraicGeometry.Picard.LineBundleOpenRepresentability
import Langlands.AlgebraicGeometry.Picard.CoherentFamilyInclusion
import Langlands.AlgebraicGeometry.CoherentSheaves.Pullback
import Mathlib.CategoryTheory.EssentialImage

/-! # The line-bundle open of an actual coherent family -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.Picard

open CoherentSheaves

variable {X Y S : Scheme.{u}}

/-- The essential image consists exactly of the actual locally free rank-one
modules, with their existing family structure. -/
lemma PicardGroupoid.toFamily_essImage_iff (p : X ⟶ Y) [Flat p]
    (M : Core (Family p)) :
    (PicardGroupoid.toFamily p).essImage M ↔ IsLocallyFreeRankOne M.of.obj := by
  constructor
  · rintro ⟨L, ⟨e⟩⟩
    exact L.of.property.of_iso ((Family.forget p).mapIso e.hom.iso)
  · intro h
    refine ⟨Core.mk ⟨M.of.obj, h⟩, ⟨?_⟩⟩
    exact asIso (⟨ObjectProperty.isoMk _ (Iso.refl M.of.obj)⟩ :
      (PicardGroupoid.toFamily p).obj (Core.mk ⟨M.of.obj, h⟩) ⟶ M)

/-- The same essential-image criterion on every actual relative space. -/
lemma PicardGroupoid.relativeToFamily_essImage_iff (f : X ⟶ S) [Flat f]
    (T : Over S) (M : FamilyGroupoid f T) :
    (PicardGroupoid.relativeToFamily f T).essImage M ↔
      IsLocallyFreeRankOne M.of.obj := by
  let : Flat ((relativeProjection f).app T) := by
    change Flat (pullback.fst T.hom f)
    infer_instance
  exact PicardGroupoid.toFamily_essImage_iff _ M

variable (f : X ⟶ S) [UniversallyClosed f] {T : Over S}
  (M : FamilyGroupoid f T)

local instance : UniversallyClosed ((relativeProjection f).app T) := by
  change UniversallyClosed (pullback.fst T.hom f)
  infer_instance

/-- The open of the test base above which this actual family is a line bundle. -/
def familyRankOneOpen : T.left.Opens :=
  rankOneBaseOpen ((relativeProjection f).app T) M.of.obj

/-- The classifying open, retained as an actual scheme over the original base. -/
def familyRankOneBase : Over S :=
  Over.mk ((familyRankOneOpen f M).ι ≫ T.hom)

/-- The actual open inclusion into the original test scheme. -/
def familyRankOneInclusion : familyRankOneBase f M ⟶ T :=
  Over.homMk (familyRankOneOpen f M).ι

@[simp]
lemma familyRankOneInclusion_left :
    (familyRankOneInclusion f M).left = (familyRankOneOpen f M).ι := rfl

/-- On the classifying open, the ordinary pullback of the actual family module
is locally free of rank one. -/
lemma familyRankOne_pullback_isLocallyFreeRankOne :
    IsLocallyFreeRankOne
      (((FamilyGroupoid.pullback f (familyRankOneInclusion f M)).obj M).of.obj) := by
  apply isLocallyFreeRankOne_pullback_over_baseOpen ((relativeProjection f).app T)
    M.of.obj ((relativeProjection f).app (familyRankOneBase f M))
    ((relativeSpace f).map (familyRankOneInclusion f M))
    (familyRankOneInclusion f M).left
    (relativeProjection_isPullback f (familyRankOneInclusion f M)).w.symm
  exact fun t ↦ t.property

/-- The actual line bundle on the relative space over the classifying open. -/
def familyRankOneLineBundle :
    LineBundle ((relativeSpace f).obj (familyRankOneBase f M)) :=
  ⟨((FamilyGroupoid.pullback f (familyRankOneInclusion f M)).obj M).of.obj,
    familyRankOne_pullback_isLocallyFreeRankOne f M⟩

/-- Including the constructed line bundle recovers the actual pulled-back family,
through an actual module-isomorphism arrow. -/
def familyRankOneLineBundleIso [Flat f] :
    (PicardGroupoid.relativeToFamily f (familyRankOneBase f M)).obj
        (Core.mk (familyRankOneLineBundle f M)) ≅
      (FamilyGroupoid.pullback f (familyRankOneInclusion f M)).obj M :=
  asIso ((FamilyGroupoid.homEquiv f (familyRankOneBase f M)).symm (Iso.refl _))

variable [LocallyOfFinitePresentation f]

local instance : LocallyOfFinitePresentation ((relativeProjection f).app T) := by
  change LocallyOfFinitePresentation (pullback.fst T.hom f)
  infer_instance

/-- Every arbitrary base change is locally free of rank one exactly when its
base map has image in the classifying open. -/
lemma familyRankOne_pullback_iff {V : Over S} (h : V ⟶ T) :
    IsLocallyFreeRankOne (((FamilyGroupoid.pullback f h).obj M).of.obj) ↔
      ∀ v : V.left, h.left v ∈ familyRankOneOpen f M :=
  isLocallyFreeRankOne_pullback_iff_mem_baseOpen (relativeProjection_isPullback f h)
    M.of.obj (FamilyGroupoid.isFlatOver f T M)

/-- The pullback of the family belongs to the essential image of the actual
Picard groupoid exactly over the classifying open. -/
lemma familyRankOne_pullback_mem_essImage_iff [Flat f] {V : Over S} (h : V ⟶ T) :
    (PicardGroupoid.relativeToFamily f V).essImage
        ((FamilyGroupoid.pullback f h).obj M) ↔
      ∀ v : V.left, h.left v ∈ familyRankOneOpen f M := by
  rw [PicardGroupoid.relativeToFamily_essImage_iff, familyRankOne_pullback_iff]

/-- A line-bundle pullback gives an actual factorization through the open. -/
def familyRankOneLift {V : Over S} (h : V ⟶ T)
    (hM : IsLocallyFreeRankOne (((FamilyGroupoid.pullback f h).obj M).of.obj)) :
    V ⟶ familyRankOneBase f M :=
  Over.homMk
    (rankOneBaseOpenLift (relativeProjection_isPullback f h) M.of.obj
      (FamilyGroupoid.isFlatOver f T M) hM)
    (by
      change _ ≫ ((familyRankOneOpen f M).ι ≫ T.hom) = V.hom
      have hf := rankOneBaseOpenLift_fac (relativeProjection_isPullback f h)
        M.of.obj (FamilyGroupoid.isFlatOver f T M) hM
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q ↦ q ≫ T.hom) hf).trans h.w))

@[reassoc (attr := simp)]
lemma familyRankOneLift_fac {V : Over S} (h : V ⟶ T)
    (hM : IsLocallyFreeRankOne (((FamilyGroupoid.pullback f h).obj M).of.obj)) :
    familyRankOneLift f M h hM ≫ familyRankOneInclusion f M = h := by
  apply Over.OverMorphism.ext
  exact rankOneBaseOpenLift_fac (relativeProjection_isPullback f h) M.of.obj
    (FamilyGroupoid.isFlatOver f T M) hM

/-- The factorization is unique among all actual maps in the full slice. -/
lemma familyRankOneLift_uniq {V : Over S} (h : V ⟶ T)
    (hM : IsLocallyFreeRankOne (((FamilyGroupoid.pullback f h).obj M).of.obj))
    (l : V ⟶ familyRankOneBase f M) (hl : l ≫ familyRankOneInclusion f M = h) :
    l = familyRankOneLift f M h hM := by
  apply Over.OverMorphism.ext
  apply rankOneBaseOpenLift_uniq (relativeProjection_isPullback f h) M.of.obj
    (FamilyGroupoid.isFlatOver f T M) hM
  exact congrArg (fun q : V ⟶ T ↦ q.left) hl

end Langlands.AlgebraicGeometry.Picard
