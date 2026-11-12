import Langlands.AlgebraicGeometry.AlgebraicSpace.SectionEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.QuasiAffineWeilRestrictionComparison

/-! # Full-slice equalizer comparisons under Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

/-- A monomorphic equalizer over the original base represents the equality
presheaf on all schemes over its test scheme. -/
def sectionEqualizerRepresentationIso {S : Scheme.{u}} {F : Presheaf S}
    {T Y : Over S} (j : Y ⟶ T) [Mono j.left] (x y : F.obj (op T))
    (hj : RepresentsEqualizer j x y) :
    (schemeYoneda T.left).obj (Over.mk j.left) ≅ sectionEqualizer x y := by
  let W : Over T.left := Over.mk j.left
  refine sectionEqualizerIsoOfIff x y ((schemeYoneda T.left).obj W) ?_ ?_
  · intro U
    constructor
    intro a b
    apply ULift.ext
    apply Over.OverMorphism.ext
    apply (cancel_mono j.left).1
    exact (Over.w a.down).trans (Over.w b.down).symm
  · intro U
    rw [← hj (sectionTestMap U)]
    constructor
    · rintro ⟨a⟩
      refine ⟨Over.homMk a.down.left (by
        change a.down.left ≫ Y.hom = U.hom ≫ T.hom
        rw [← Over.w j, ← Category.assoc]
        exact congrArg (fun a ↦ a ≫ T.hom) (Over.w a.down)), ?_⟩
      apply Over.OverMorphism.ext
      exact Over.w a.down
    · rintro ⟨a, ha⟩
      exact ⟨⟨Over.homMk a.left (congrArg Over.Hom.left ha)⟩⟩

namespace WeilRestrictionEqualizer

variable {S S' T T' : Scheme.{u}}
variable {g : S' ⟶ S} {f : T ⟶ S} {f' : T' ⟶ S'} {g' : T' ⟶ T}
variable (h : IsPullback f' g' g f)

/-- The specified upper test scheme is the actual pullback over the old base. -/
def baseTestIso : Over.mk f' ≅ (Over.pullback g).obj (Over.mk f) :=
  Over.isoMk h.flip.isoPullback h.flip.isoPullback_hom_snd

@[reassoc (attr := simp)]
theorem baseTestIso_hom_fst :
    (baseTestIso h).hom.left ≫ pullback.fst f g = g' :=
  h.flip.isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem baseTestIso_hom_snd :
    (baseTestIso h).hom.left ≫ pullback.snd f g = f' :=
  h.flip.isoPullback_hom_snd

/-- The cartesian test comparison respects the map to the scheme carrying
the original sections. -/
theorem sectionTestMap_comp_baseTestIso (U : Over T) :
    sectionTestMap (T := Over.mk f') ((Over.pullback g').obj U) ≫ (baseTestIso h).hom =
      (WeilRestrictionBaseChange.testIso h U).hom ≫
        (Over.pullback g).map (sectionTestMap (T := Over.mk f) U) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc,
      Over.pullback_map_left, pullback.lift_fst, Over.homMk_left, sectionTestMap]
    change pullback.snd U.hom g' ≫ (baseTestIso h).hom.left ≫ pullback.fst f g =
      (WeilRestrictionBaseChange.testIso h U).hom.left ≫
        pullback.fst (U.hom ≫ f) g ≫ U.hom
    rw [baseTestIso_hom_fst, WeilRestrictionBaseChange.testIso_hom_fst_assoc]
    exact (pullback.condition (f := U.hom) (g := g')).symm
  · simp [sectionTestMap, Over.pullback_map_left, Category.assoc,
      WeilRestrictionBaseChange.testIso_hom_snd]

/-- A cartesian square identifies the restricted upper equality locus with
the equality locus in the full Weil presheaf. -/
def sectionEqualizerWeilIso (F : Presheaf S')
    (x y : F.obj (op ((Over.pullback g).obj (Over.mk f)))) :
    (Over.pullback g').op ⋙ sectionEqualizer
      (F.map (baseTestIso h).hom.op x) (F.map (baseTestIso h).hom.op y) ≅
      sectionEqualizer (F := (Over.pullback g).op ⋙ F) (T := Over.mk f) x y := by
  let x' := F.map (baseTestIso h).hom.op x
  let y' := F.map (baseTestIso h).hom.op y
  refine sectionEqualizerIsoOfIff (F := (Over.pullback g).op ⋙ F) (T := Over.mk f)
    x y ((Over.pullback g').op ⋙ sectionEqualizer x' y')
    (fun U ↦ sectionEqualizer_obj_subsingleton x' y' ((Over.pullback g').op.obj U)) ?_
  intro U
  have hi : Nonempty ((sectionEqualizer x' y').obj (op ((Over.pullback g').obj U))) ↔
      F.map (sectionTestMap ((Over.pullback g').obj U)).op x' =
        F.map (sectionTestMap ((Over.pullback g').obj U)).op y' :=
    ⟨fun ⟨a⟩ ↦ a.2, fun hw ↦
      ⟨⟨⟨Over.homMk ((Over.pullback g').obj U).hom (by simp)⟩, hw⟩⟩⟩
  rw [hi]
  change F.map (sectionTestMap ((Over.pullback g').obj U)).op
      (F.map (baseTestIso h).hom.op x) =
      F.map (sectionTestMap ((Over.pullback g').obj U)).op
        (F.map (baseTestIso h).hom.op y) ↔
    F.map ((Over.pullback g).map (sectionTestMap U)).op x =
      F.map ((Over.pullback g).map (sectionTestMap U)).op y
  rw [← F.map_comp_apply, ← F.map_comp_apply, ← op_comp,
    sectionTestMap_comp_baseTestIso, op_comp, F.map_comp_apply, F.map_comp_apply]
  exact (ConcreteCategory.bijective_of_isIso
    (F.map (WeilRestrictionBaseChange.testIso h U).hom.op)).injective.eq_iff

/-- Any scheme representation of the restriction of a monomorphic upper
equalizer represents the equalizer in the original full Weil presheaf. -/
def sectionEqualizerWeilRepresentationIso (F : Presheaf S')
    (x y : F.obj (op ((Over.pullback g).obj (Over.mk f))))
    {Y : Over S'} (j : Y ⟶ Over.mk f') [Mono j.left]
    (hj : RepresentsEqualizer j
      (F.map (baseTestIso h).hom.op x) (F.map (baseTestIso h).hom.op y))
    (W : Over T)
    (eW : (schemeYoneda T).obj W ≅
      (Over.pullback g').op ⋙ (schemeYoneda T').obj (Over.mk j.left)) :
    (schemeYoneda T).obj W ≅
      sectionEqualizer (F := (Over.pullback g).op ⋙ F) (T := Over.mk f) x y :=
  eW ≪≫ Functor.isoWhiskerLeft (Over.pullback g').op
    (sectionEqualizerRepresentationIso j _ _ hj) ≪≫ sectionEqualizerWeilIso h F x y

end WeilRestrictionEqualizer

section Affine

open PointTopology
open WeilRestrictionEqualizer

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable {S S' : Scheme.{u}} {g : S' ⟶ S}
  {f : Spec (CommRingCat.of A) ⟶ S} {f' : Spec (CommRingCat.of B) ⟶ S'}
  (h : IsPullback f' (Spec.algebraMap A B) g f) (F : Presheaf S')
  (x y : F.obj (op ((Over.pullback g).obj (Over.mk f))))
  (Y : Over (Spec (CommRingCat.of B))) [Mono Y.hom]
  [Y.left.IsQuasiAffine] [LocallyOfFiniteType Y.hom]
  (hY : RepresentsEqualizer (sectionTestMap (T := Over.mk f') Y)
    (F.map (baseTestIso h).hom.op x) (F.map (baseTestIso h).hom.op y))

/-- The actual quasi-affine Weil scheme represents the equalizer of sections
of the full restricted presheaf over an affine test base. -/
def quasiAffineSectionEqualizerWeilIso :
    (schemeYoneda _).obj (affineChartWeilRestriction A B Y) ≅
      sectionEqualizer (F := (Over.pullback g).op ⋙ F) (T := Over.mk f) x y := by
  letI : Mono (sectionTestMap (T := Over.mk f') Y).left := ‹Mono Y.hom›
  exact sectionEqualizerWeilRepresentationIso h F x y
    (sectionTestMap (T := Over.mk f') Y) hY
    (affineChartWeilRestriction A B Y)
    (quasiAffineWeilRestrictionPresheafIso A B Y)

include hY in
/-- The affine-test representation has a quasi-compact structure map. -/
theorem exists_quasiCompact_sectionEqualizer_weil :
    ∃ W : Over (Spec (CommRingCat.of A)),
      Nonempty ((schemeYoneda _).obj W ≅
        sectionEqualizer (F := (Over.pullback g).op ⋙ F) (T := Over.mk f) x y) ∧
      QuasiCompact W.hom :=
  ⟨affineChartWeilRestriction A B Y,
    ⟨quasiAffineSectionEqualizerWeilIso A B h F x y Y hY⟩,
    (quasiAffineWeilRestriction_schemeProperties A B Y).2.1⟩

end Affine

end Langlands.AlgebraicGeometry.AlgebraicSpace
