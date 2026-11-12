import Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasAssembly
import Langlands.AlgebraicGeometry.Stacks.SchemeAtlas
import Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart
import Langlands.AlgebraicGeometry.Picard.PointFiberTestReduction
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberAtlasRestriction
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberObjectIso
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberTestChange

/-! # Maps into representing schemes of actual point fibres -/

universe u

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Stacks

open Langlands.CategoryTheory.PseudofunctorPointFiber
open Langlands.CategoryTheory.PseudofunctorPointFiberAtlasRestriction

variable {S : Scheme.{u}} {F : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1}}

section Representation

variable {U T : Over S} {ξ : F.obj (.mk (op U))} {η : F.obj (.mk (op T))}
  {P : Over T.left}
  (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf F ξ η)

/-- A representation identifies maps into the representing scheme with fibre points. -/
def pointEquiv (Z : Over T.left) : (Z ⟶ P) ≃ PointFiberPoints F ξ η Z :=
  Equiv.ulift.symm.trans (e.app (op Z)).toEquiv

/-- The identification is natural in the test scheme. -/
lemma pointEquiv_comp {Z Z' : Over T.left} (q : Z' ⟶ Z) (g : Z ⟶ P) :
    pointEquiv e Z' (q ≫ g) =
      restrict F ξ η (T.iteratedSliceBackward.map q) (pointEquiv e Z g) :=
  ConcreteCategory.congr_hom (e.hom.naturality q.op)
    (ULift.up.{u + 1} g : ((AlgebraicSpace.schemeYoneda T.left).obj P).obj (op Z))

/-- The underlying map from a representing scheme to the chart. -/
def universalMap : P.left ⟶ U.left :=
  (pointEquiv e P (𝟙 P)).1.left

/-- The point classified by a map into the representing scheme has the
composite map to the chart. -/
lemma pointEquiv_fst_left {Z : Over T.left} (g : Z ⟶ P) :
    (pointEquiv e Z g).1.left = g.left ≫ universalMap e := by
  have h := pointEquiv_comp e g (𝟙 P)
  rw [Category.comp_id] at h
  rw [h]
  rfl

include e in
/-- Every scheme over the test carrying a fibre point maps into the representing
scheme, so its image lies in the image of the representing scheme. -/
lemma range_subset_of_point {Z : Over T.left} (x : PointFiberPoints F ξ η Z) :
    Set.range Z.hom.base ⊆ Set.range P.hom.base := by
  rintro _ ⟨z, rfl⟩
  let h : Z ⟶ P := (pointEquiv e Z).symm x
  refine ⟨h.left.base z, ?_⟩
  rw [← Scheme.Hom.comp_apply, Over.w h]

end Representation

section Restriction

variable {U V T : Over S} {ξ : F.obj (.mk (op U))} {η : F.obj (.mk (op T))}
  {P : Over T.left}
  (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf F ξ η)
  (j : V ⟶ U)

/-- The family restricted along a map of charts. -/
abbrev restrictObj (j : V ⟶ U) (ξ : F.obj (.mk (op U))) : F.obj (.mk (op V)) :=
  (F.map j.op.toLoc).toFunctor.obj ξ

/-- The part of a representing scheme that maps into the restricted chart. -/
def restrictScheme : Over T.left :=
  Over.mk (pullback.fst (universalMap e) j.left ≫ P.hom)

/-- The inclusion of that part into the representing scheme. -/
def restrictSchemeι : restrictScheme e j ⟶ P :=
  Over.homMk (pullback.fst (universalMap e) j.left) rfl

/-- A restricted point gives a map into the restricted representing scheme. -/
def toRestrictScheme (Z : Over T.left)
    (x : PointFiberPoints F (restrictObj j ξ) η Z) : Z ⟶ restrictScheme e j :=
  let x' : PointFiberPoints F ξ η Z :=
    mapPoints F j ξ η (T.iteratedSliceBackward.obj Z) x
  let g : Z ⟶ P := (pointEquiv e Z).symm x'
  Over.homMk (pullback.lift g.left x.1.left (by
    rw [← pointEquiv_fst_left e g]
    simp only [g, Equiv.apply_symm_apply]
    rfl)) (by
    simp only [restrictScheme, Over.mk_hom]
    rw [pullback.lift_fst_assoc]
    exact Over.w g)

@[reassoc (attr := simp)]
lemma toRestrictScheme_left_fst (Z : Over T.left)
    (x : PointFiberPoints F (restrictObj j ξ) η Z) :
    (toRestrictScheme e j Z x).left ≫ pullback.fst (universalMap e) j.left =
      ((pointEquiv e Z).symm (mapPoints F j ξ η
        (T.iteratedSliceBackward.obj Z) x)).left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma toRestrictScheme_left_snd (Z : Over T.left)
    (x : PointFiberPoints F (restrictObj j ξ) η Z) :
    (toRestrictScheme e j Z x).left ≫ pullback.snd (universalMap e) j.left = x.1.left :=
  pullback.lift_snd _ _ _

lemma toRestrictScheme_comp_ι (Z : Over T.left)
    (x : PointFiberPoints F (restrictObj j ξ) η Z) :
    toRestrictScheme e j Z x ≫ restrictSchemeι e j =
      (pointEquiv e Z).symm (mapPoints F j ξ η (T.iteratedSliceBackward.obj Z) x) := by
  ext1
  rw [Over.comp_left]
  exact toRestrictScheme_left_fst e j Z x

lemma toRestrictScheme_injective [Mono j] (Z : Over T.left) :
    Function.Injective (toRestrictScheme e j Z) := by
  intro x y h
  have h1 := congrArg (· ≫ restrictSchemeι e j) h
  simp only [toRestrictScheme_comp_ι] at h1
  exact mapPoints_injective F j ξ η _ ((pointEquiv e Z).symm.injective h1)

/-- A fibre point whose map factors through the restricted chart comes from a
restricted fibre point with the given factorization. -/
lemma exists_mapPoints_eq (Z : Over T.left) (y : PointFiberPoints F ξ η Z)
    (a : (T.iteratedSliceBackward.obj Z).left ⟶ V) (ha : a ≫ j = y.1) :
    ∃ x : PointFiberPoints F (restrictObj j ξ) η Z,
      mapPoints F j ξ η (T.iteratedSliceBackward.obj Z) x = y ∧ x.1 = a := by
  rcases y with ⟨b, e⟩
  dsimp only at ha
  subst ha
  exact ⟨⟨a, (atlasComparison F j ξ a).symm ≪≫ e⟩, by simp [mapPoints], rfl⟩

lemma toRestrictScheme_surjective (Z : Over T.left) :
    Function.Surjective (toRestrictScheme e j Z) := by
  intro h
  let g : Z ⟶ P := h ≫ restrictSchemeι e j
  let y := pointEquiv e Z g
  have hy : y.1.left = (h.left ≫ pullback.snd (universalMap e) j.left) ≫ j.left := by
    rw [pointEquiv_fst_left]
    change (h.left ≫ pullback.fst (universalMap e) j.left) ≫ universalMap e = _
    rw [Category.assoc, pullback.condition, Category.assoc]
  let b : (T.iteratedSliceBackward.obj Z).left ⟶ V :=
    Over.homMk (h.left ≫ pullback.snd (universalMap e) j.left) (by
      have hw := Over.w y.1
      rw [hy] at hw
      rw [← Over.w j]
      simpa only [Category.assoc] using hw)
  have hb : b ≫ j = y.1 := by
    ext1
    rw [Over.comp_left, hy]
    rfl
  obtain ⟨x, hx, hxb⟩ := exists_mapPoints_eq j Z y b hb
  refine ⟨x, ?_⟩
  ext1
  apply pullback.hom_ext
  · rw [toRestrictScheme_left_fst, hx]
    simp [y, g, restrictSchemeι]
  · rw [toRestrictScheme_left_snd, hxb]
    rfl

/-- Restriction of fibre points along a test map corresponds to composition. -/
lemma toRestrictScheme_restrict {Z Z' : Over T.left} (q : Z' ⟶ Z)
    (x : PointFiberPoints F (restrictObj j ξ) η Z) :
    toRestrictScheme e j Z'
        (restrict F (restrictObj j ξ) η (T.iteratedSliceBackward.map q) x) =
      q ≫ toRestrictScheme e j Z x := by
  ext1
  apply pullback.hom_ext
  · rw [toRestrictScheme_left_fst]
    erw [mapPoints_restrict F j ξ η (T.iteratedSliceBackward.map q) x]
    have h := pointEquiv_comp e q ((pointEquiv e Z).symm (mapPoints F j ξ η
      (T.iteratedSliceBackward.obj Z) x))
    rw [Equiv.apply_symm_apply] at h
    rw [← h, Equiv.symm_apply_apply]
    simp
  · rw [toRestrictScheme_left_snd]
    simp
    rfl

/-- The part of a representing scheme over a restricted chart represents the
fibre of the restricted family. -/
def restrictIso [Mono j] :
    (AlgebraicSpace.schemeYoneda T.left).obj (restrictScheme e j) ≅
      pointFiberPresheaf F (restrictObj j ξ) η :=
  (NatIso.ofComponents (fun Z ↦ ((Equiv.ofBijective
      (toRestrictScheme e j Z.unop) ⟨toRestrictScheme_injective e j Z.unop,
        toRestrictScheme_surjective e j Z.unop⟩).trans Equiv.ulift.symm).toIso) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (toRestrictScheme_restrict e j q.unop x))).symm

end Restriction

section Comparisons

variable {U T T' : Over S}

/-- Isomorphic chart objects have isomorphic actual point fibres. -/
def pointFiberPresheafIsoOfChartIso {ξ ξ' : F.obj (.mk (op U))} (c : ξ ≅ ξ')
    (η : F.obj (.mk (op T))) :
    pointFiberPresheaf F ξ η ≅ pointFiberPresheaf F ξ' η :=
  Functor.isoWhiskerLeft T.iteratedSliceBackward.op
    (Langlands.CategoryTheory.PseudofunctorPointFiberObjectIso.presheafIso F c η)

/-- Isomorphic test objects have isomorphic actual point fibres. -/
def pointFiberPresheafIsoOfTestIso (ξ : F.obj (.mk (op U))) {η η' : F.obj (.mk (op T))}
    (c : η ≅ η') :
    pointFiberPresheaf F ξ η ≅ pointFiberPresheaf F ξ η' :=
  Functor.isoWhiskerLeft T.iteratedSliceBackward.op
    (Langlands.CategoryTheory.PseudofunctorPointFiberTestChange.isoPresheafIso F ξ c)

/-- Pulling back the test object restricts the actual point fibre along `Over.map`. -/
def pointFiberPresheafBaseChangeIso (ξ : F.obj (.mk (op U))) (g : T' ⟶ T)
    (η : F.obj (.mk (op T))) :
    pointFiberPresheaf F ξ (restrictObj g η) ≅
      (Over.map g.left).op ⋙ pointFiberPresheaf F ξ η :=
  Functor.isoWhiskerLeft T'.iteratedSliceBackward.op
      (Langlands.CategoryTheory.PseudofunctorPointFiberTestChange.basePresheafIso F ξ η g) ≪≫
    Functor.isoWhiskerRight (NatIso.op (Picard.PicardGroupoid.iteratedSliceMapIso g)).symm
      (presheaf F ξ η)

/-- The pullback of a representing scheme represents the pulled-back test object. -/
def pullbackRepresentationIso (ξ : F.obj (.mk (op U))) (g : T' ⟶ T)
    {η : F.obj (.mk (op T))} {P : Over T.left}
    (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf F ξ η) :
    (AlgebraicSpace.schemeYoneda T'.left).obj ((Over.pullback g.left).obj P) ≅
      pointFiberPresheaf F ξ (restrictObj g η) :=
  Picard.PicardGroupoid.schemeYonedaPullbackIso g.left P ≪≫
    Functor.isoWhiskerLeft (Over.map g.left).op e ≪≫
      (pointFiberPresheafBaseChangeIso ξ g η).symm

/-- A chart point over a test map, with an actual isomorphism of pulled-back
objects, lies in the image of every representing scheme. -/
lemma mem_range_of_chartPoint {ξ : F.obj (.mk (op U))} {η : F.obj (.mk (op T))}
    {P : Over T.left}
    (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf F ξ η)
    (g : T' ⟶ T) (a : T' ⟶ U) (c : restrictObj a ξ ≅ restrictObj g η) (x : T'.left) :
    g.left.base x ∈ Set.range P.hom.base := by
  let Z : Over T.left := Over.mk g.left
  let ζ : (T.iteratedSliceBackward.obj Z).left ⟶ T' :=
    Over.homMk (𝟙 _) (by simp [Z])
  have hζ : ζ ≫ g = (T.iteratedSliceBackward.obj Z).hom := by
    ext1
    simp [ζ, Z]
  let y : PointFiberPoints F ξ η Z :=
    ⟨ζ ≫ a, pullIso c ζ (ζ ≫ a) (T.iteratedSliceBackward.obj Z).hom rfl hζ⟩
  exact range_subset_of_point e y ⟨x, rfl⟩

end Comparisons

section Coproduct

open AlgebraicSpace.CoproductChart

variable {ι : Type u} (V : ι → Over S) {T : Over S}

/-- A representing scheme of a coproduct chart is smooth over the test when the
restrictions of the chart object to the components have smooth representing
schemes against the same test object. -/
theorem smooth_of_coproductChart (ξ : F.obj (.mk (op (sigmaOver V))))
    (ξs : ∀ i, F.obj (.mk (op (V i)))) (c : ∀ i, restrictObj (sigmaOverι V i) ξ ≅ ξs i)
    (η : F.obj (.mk (op T)))
    (hs : ∀ i, ∃ Q : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj Q ≅
        pointFiberPresheaf F (ξs i) η) ∧ Smooth Q.hom)
    {P : Over T.left}
    (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅ pointFiberPresheaf F ξ η) :
    Smooth P.hom := by
  refine IsZariskiLocalAtSource.of_openCover
    ((sigmaOpenCover (fun i ↦ (V i).left)).pullback₁ (universalMap e)) (fun i ↦ ?_)
  have : Mono (sigmaOverι V i) :=
    (Over.forget S).mono_of_mono_map (show Mono (sigmaOverι V i).left from inferInstance)
  obtain ⟨Q, ⟨eQ⟩, hQ⟩ := hs i
  let φ := Picard.PicardGroupoid.representingIso (restrictIso e (sigmaOverι V i) ≪≫
    pointFiberPresheafIsoOfChartIso (c i) η) eQ
  have hsm : Smooth (restrictScheme e (sigmaOverι V i)).hom := by
    rw [← Over.w φ.hom]
    infer_instance
  exact hsm

end Coproduct

end Langlands.AlgebraicGeometry.Stacks
