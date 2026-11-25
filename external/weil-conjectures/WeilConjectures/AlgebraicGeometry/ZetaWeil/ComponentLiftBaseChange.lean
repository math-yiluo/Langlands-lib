/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ZetaWeil.ComponentRelativeProfiniteSite
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.Relative.RelativeComponentLiftPullbackSpace
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Base change of affine relative component lifts

Source: Hemo--Richarz--Scholbach, construction preceding (4.1), pp. 8--9;
Bhatt--Scholze, Lemma 2.2.8 and its more precise statement
(blueprint: lem-zl-component-lift-base-change).

The relative lift and its coordinate are taken from the characterized functor of
`component_relative_profinite_site`. The universal property determines that functor up to
unique coordinate-preserving isomorphism. No arbitrary affine test object is substituted.
Mathlib's `Over.pullback f` orders the factors as `X_E ×_X Y`.
The symmetry isomorphism identifies this with the displayed `Y ×_X X_E` in the source.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry.ProEtale

/-- The relative component-lift functor, with values in schemes over the affine base.
Source: Hemo--Richarz--Scholbach, before (4.1)
(blueprint: lem-zl-component-lift-base-change).
The chosen witness is characterized by the universal property in the cited theorem. -/
noncomputable def relativeComponentLift (T : Scheme.{u}) [IsAffine T] :
    Over (affineComponentSpace T) ⥤ Over T :=
  (component_relative_profinite_site T).choose ⋙ Scheme.ProEt.forget T

/-- The continuous profinite coordinate of the characterized relative lift.
Source: Hemo--Richarz--Scholbach, before (4.1); Bhatt--Scholze, Lemma 2.2.8
(blueprint: lem-zl-component-lift-base-change). -/
noncomputable def relativeComponentCoordinate (T : Scheme.{u}) [IsAffine T]
    (E : Over (affineComponentSpace T)) :
    C(((relativeComponentLift T).obj E).left, E.left) :=
  (component_relative_profinite_site T).choose_spec.2.1.choose E

/-- The map on the actual quotient spaces of connected components induced by a scheme map.
Source: Hemo--Richarz--Scholbach, naturality of the construction before (4.1)
(blueprint: lem-zl-component-lift-base-change). -/
def affineComponentMap {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X) :
    affineComponentSpace Y ⟶ affineComponentSpace X :=
  ConcreteCategory.ofHom
    (⟨f.continuous.connectedComponentsMap, f.continuous.connectedComponentsMap_continuous⟩ :
      C(affineComponentSpace Y, affineComponentSpace X))

section

set_option backward.isDefEq.respectTransparency false

private theorem coordinate_base (T : Scheme.{u}) [IsAffine T]
    (E : Over (affineComponentSpace T)) (x : ((relativeComponentLift T).obj E).left) :
    E.hom (relativeComponentCoordinate T E x) =
      ConnectedComponents.mk (((relativeComponentLift T).obj E).hom x) :=
  (component_relative_profinite_site T).choose_spec.2.1.choose_spec.1 E x

private theorem coordinate_map (T : Scheme.{u}) [IsAffine T]
    {E E' : Over (affineComponentSpace T)} (a : E ⟶ E')
    (x : ((relativeComponentLift T).obj E).left) :
    relativeComponentCoordinate T E' (((relativeComponentLift T).map a).left x) =
      a.left (relativeComponentCoordinate T E x) :=
  (component_relative_profinite_site T).choose_spec.2.1.choose_spec.2.1 E E' a x

private theorem lift_exists (T : Scheme.{u}) [IsAffine T]
    (W : Scheme.{u}) (b : W ⟶ T) (E : Over (affineComponentSpace T))
    (g : C(W, E.left)) (hg : ∀ w, E.hom (g w) = ConnectedComponents.mk (b w)) :
    ∃! m : W ⟶ ((relativeComponentLift T).obj E).left,
      m ≫ ((relativeComponentLift T).obj E).hom = b ∧
      ∀ w, relativeComponentCoordinate T E (m w) = g w := by
  obtain ⟨m, hm, hu⟩ :=
    (component_relative_profinite_site T).choose_spec.2.1.choose_spec.2.2
      (Over.mk b) E g hg
  refine ⟨m.left, ⟨m.w, hm⟩, ?_⟩
  intro n hn
  exact congrArg (fun k ↦ k.left) (hu (Over.homMk n hn.1) hn.2)

private theorem lift_ext (T : Scheme.{u}) [IsAffine T]
    {W : Scheme.{u}} {E : Over (affineComponentSpace T)}
    (a b : W ⟶ ((relativeComponentLift T).obj E).left)
    (hab : a ≫ ((relativeComponentLift T).obj E).hom =
      b ≫ ((relativeComponentLift T).obj E).hom)
    (hp : ∀ w, relativeComponentCoordinate T E (a w) =
      relativeComponentCoordinate T E (b w)) : a = b := by
  let g : C(W, E.left) := (relativeComponentCoordinate T E).comp ⟨b, b.continuous⟩
  have hg : ∀ w, E.hom (g w) = ConnectedComponents.mk
      ((b ≫ ((relativeComponentLift T).obj E).hom) w) := fun w ↦ coordinate_base T E (b w)
  obtain ⟨m, hm, hu⟩ := lift_exists T W _ E g hg
  exact (hu a ⟨hab, hp⟩).trans (hu b ⟨rfl, fun _ ↦ rfl⟩).symm

private noncomputable def profinitePullbackHomeo {P Q E : Profinite.{u}}
    (e : E ⟶ P) (h : Q ⟶ P) :
    ↑(pullback e h : Profinite.{u}) ≃ₜ {z : E × Q | e z.1 = h z.2} :=
  CompHausLike.homeoOfIso
    ((pullback.isLimit e h).conePointUniqueUpToIso (CompHausLike.pullback.isLimit e h))

private theorem profinitePullbackHomeo_fst {P Q E : Profinite.{u}}
    (e : E ⟶ P) (h : Q ⟶ P) (z : (pullback e h : Profinite.{u})) :
    (profinitePullbackHomeo e h z).val.1 = pullback.fst e h z := by
  exact ConcreteCategory.congr_hom
    ((pullback.isLimit e h).conePointUniqueUpToIso_hom_comp
      (CompHausLike.pullback.isLimit e h) WalkingCospan.left) z

private theorem profinitePullbackHomeo_snd {P Q E : Profinite.{u}}
    (e : E ⟶ P) (h : Q ⟶ P) (z : (pullback e h : Profinite.{u})) :
    (profinitePullbackHomeo e h z).val.2 = pullback.snd e h z := by
  exact ConcreteCategory.congr_hom
    ((pullback.isLimit e h).conePointUniqueUpToIso_hom_comp
      (CompHausLike.pullback.isLimit e h) WalkingCospan.right) z

private theorem profinite_pullback_ext {P Q E : Profinite.{u}}
    (e : E ⟶ P) (h : Q ⟶ P) {a b : (pullback e h : Profinite.{u})}
    (h₁ : pullback.fst e h a = pullback.fst e h b)
    (h₂ : pullback.snd e h a = pullback.snd e h b) : a = b := by
  apply (profinitePullbackHomeo e h).injective
  apply Subtype.ext
  apply Prod.ext
  · simpa only [profinitePullbackHomeo_fst] using h₁
  · simpa only [profinitePullbackHomeo_snd] using h₂

private theorem component_map_mk {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (y : Y) :
    affineComponentMap f (ConnectedComponents.mk y) = ConnectedComponents.mk (f y) := rfl

private noncomputable def comparisonCoordinate {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) (E : Over (affineComponentSpace X)) :
    C(((relativeComponentLift X ⋙ Over.pullback f).obj E).left,
      ((Over.pullback (affineComponentMap f)).obj E).left) := by
  let a := pullback.fst ((relativeComponentLift X).obj E).hom f
  let b := pullback.snd ((relativeComponentLift X).obj E).hom f
  have hc (z : ((relativeComponentLift X ⋙ Over.pullback f).obj E).left) :
      E.hom (relativeComponentCoordinate X E (a z)) =
        affineComponentMap f (ConnectedComponents.mk (b z)) := by
    rw [coordinate_base, component_map_mk]
    exact congrArg ConnectedComponents.mk
      (congrArg (fun k : pullback ((relativeComponentLift X).obj E).hom f ⟶ X ↦ k z)
        (pullback.condition (f := ((relativeComponentLift X).obj E).hom) (g := f)))
  refine ⟨fun z ↦ (profinitePullbackHomeo E.hom (affineComponentMap f)).symm
    ⟨(relativeComponentCoordinate X E (a z), ConnectedComponents.mk (b z)), hc z⟩, ?_⟩
  exact (profinitePullbackHomeo E.hom (affineComponentMap f)).symm.continuous.comp
      (((relativeComponentCoordinate X E).continuous.comp a.continuous).prodMk
        (ConnectedComponents.continuous_coe.comp b.continuous) |>.subtype_mk (fun z ↦ hc z))

private theorem comparisonCoordinate_fst {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (E : Over (affineComponentSpace X))
    (z : ((relativeComponentLift X ⋙ Over.pullback f).obj E).left) :
    pullback.fst E.hom (affineComponentMap f) (comparisonCoordinate f E z) =
      relativeComponentCoordinate X E (pullback.fst ((relativeComponentLift X).obj E).hom f z) := by
  rw [← profinitePullbackHomeo_fst]
  exact congrArg (fun t ↦ t.val.1)
    ((profinitePullbackHomeo E.hom (affineComponentMap f)).apply_symm_apply _)

private theorem comparisonCoordinate_snd {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (E : Over (affineComponentSpace X))
    (z : ((relativeComponentLift X ⋙ Over.pullback f).obj E).left) :
    pullback.snd E.hom (affineComponentMap f) (comparisonCoordinate f E z) =
      ConnectedComponents.mk (pullback.snd ((relativeComponentLift X).obj E).hom f z) := by
  rw [← profinitePullbackHomeo_snd]
  exact congrArg (fun t ↦ t.val.2)
    ((profinitePullbackHomeo E.hom (affineComponentMap f)).apply_symm_apply _)

private noncomputable def comparisonHom {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (E : Over (affineComponentSpace X)) :
    (relativeComponentLift X ⋙ Over.pullback f).obj E ⟶
      (Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj E :=
  Over.homMk (lift_exists Y _ _ _ (comparisonCoordinate f E)
    (comparisonCoordinate_snd f E)).choose
    (lift_exists Y _ _ _ (comparisonCoordinate f E)
      (comparisonCoordinate_snd f E)).choose_spec.1.1

private theorem comparisonHom_coordinate {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (E : Over (affineComponentSpace X))
    (z : ((relativeComponentLift X ⋙ Over.pullback f).obj E).left) :
    relativeComponentCoordinate Y _ ((comparisonHom f E).left z) =
      comparisonCoordinate f E z :=
  (lift_exists Y _ _ _ (comparisonCoordinate f E)
    (comparisonCoordinate_snd f E)).choose_spec.1.2 z

private noncomputable def reverseCoordinate {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (E : Over (affineComponentSpace X)) :
    C(((Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj E).left,
      E.left) :=
  ⟨fun z ↦ pullback.fst E.hom (affineComponentMap f) (relativeComponentCoordinate Y _ z),
    (pullback.fst E.hom (affineComponentMap f)).hom.hom.continuous.comp
      (relativeComponentCoordinate Y _).continuous⟩

private theorem reverseCoordinate_base {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (E : Over (affineComponentSpace X))
    (z : ((Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj E).left) :
    E.hom (reverseCoordinate f E z) = ConnectedComponents.mk
      ((((Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj E).hom ≫ f) z) := by
  change E.hom (pullback.fst E.hom (affineComponentMap f)
    (relativeComponentCoordinate Y _ z)) = _
  erw [← ConcreteCategory.comp_apply, pullback.condition, ConcreteCategory.comp_apply]
  erw [coordinate_base Y ((Over.pullback (affineComponentMap f)).obj E)]
  rfl

private noncomputable def reverseHom {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (E : Over (affineComponentSpace X)) :
    (Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj E ⟶
      (relativeComponentLift X ⋙ Over.pullback f).obj E :=
  Over.homMk (pullback.lift
    (lift_exists X _ _ E (reverseCoordinate f E) (reverseCoordinate_base f E)).choose
    (((Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj E).hom)
    (lift_exists X _ _ E (reverseCoordinate f E)
      (reverseCoordinate_base f E)).choose_spec.1.1) (by simp)

private theorem reverseHom_fst_coordinate {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) (E : Over (affineComponentSpace X))
    (z : ((Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj E).left) :
    relativeComponentCoordinate X E
        (pullback.fst ((relativeComponentLift X).obj E).hom f ((reverseHom f E).left z)) =
      pullback.fst E.hom (affineComponentMap f) (relativeComponentCoordinate Y _ z) := by
  dsimp only [reverseHom]
  erw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  exact (lift_exists X _ _ E (reverseCoordinate f E)
    (reverseCoordinate_base f E)).choose_spec.1.2 z

private theorem comparison_ext {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (E : Over (affineComponentSpace X)) (W : Over Y)
    (a b : W ⟶ (Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj E)
    (h : ∀ z, pullback.fst E.hom (affineComponentMap f)
        (relativeComponentCoordinate Y _ (a.left z)) =
      pullback.fst E.hom (affineComponentMap f)
        (relativeComponentCoordinate Y _ (b.left z))) : a = b := by
  apply Over.OverMorphism.ext
  apply lift_ext Y a.left b.left (a.w.trans b.w.symm)
  intro z
  apply profinite_pullback_ext E.hom (affineComponentMap f) (h z)
  erw [coordinate_base Y ((Over.pullback (affineComponentMap f)).obj E),
    coordinate_base Y ((Over.pullback (affineComponentMap f)).obj E)]
  exact congrArg ConnectedComponents.mk
    ((congrArg (fun k ↦ k z) a.w).trans (congrArg (fun k ↦ k z) b.w).symm)

private theorem comparisonHom_reverseHom {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) (E : Over (affineComponentSpace X)) :
    comparisonHom f E ≫ reverseHom f E = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply lift_ext X
    · rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (comparisonHom f E ≫ reverseHom f E).left ≫
          pullback.snd ((relativeComponentLift X).obj E).hom f ≫ f = _
      rw [← Category.assoc]
      erw [(comparisonHom f E ≫ reverseHom f E).w]
      simp [pullback.condition]
    · intro z
      change relativeComponentCoordinate X E
        (pullback.fst ((relativeComponentLift X).obj E).hom f
          ((reverseHom f E).left ((comparisonHom f E).left z))) = _
      erw [reverseHom_fst_coordinate, comparisonHom_coordinate, comparisonCoordinate_fst]
      rfl
  · exact (comparisonHom f E ≫ reverseHom f E).w

private theorem reverseHom_comparisonHom {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) (E : Over (affineComponentSpace X)) :
    reverseHom f E ≫ comparisonHom f E = 𝟙 _ := by
  apply comparison_ext f E
  intro z
  change pullback.fst E.hom (affineComponentMap f)
    (relativeComponentCoordinate Y _
      ((comparisonHom f E).left ((reverseHom f E).left z))) = _
  erw [comparisonHom_coordinate, comparisonCoordinate_fst, reverseHom_fst_coordinate]
  rfl

private noncomputable def comparisonIso {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) :
    relativeComponentLift X ⋙ Over.pullback f ≅
      Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y :=
  NatIso.ofComponents (fun E ↦
    ⟨comparisonHom f E, reverseHom f E,
      comparisonHom_reverseHom f E, reverseHom_comparisonHom f E⟩) (by
    intro E E' a
    apply comparison_ext f E'
    intro z
    change pullback.fst E'.hom (affineComponentMap f)
        (relativeComponentCoordinate Y _ ((comparisonHom f E').left
          (((Over.pullback f).map ((relativeComponentLift X).map a)).left z))) =
      pullback.fst E'.hom (affineComponentMap f)
        (relativeComponentCoordinate Y _ (((relativeComponentLift Y).map
          ((Over.pullback (affineComponentMap f)).map a)).left ((comparisonHom f E).left z)))
    erw [comparisonHom_coordinate, comparisonCoordinate_fst, coordinate_map]
    simp only [Over.pullback_map_left]
    erw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, coordinate_map]
    erw [← ConcreteCategory.comp_apply, pullback.lift_fst, ConcreteCategory.comp_apply,
      comparisonHom_coordinate, comparisonCoordinate_fst]
    rfl)

private theorem component_map_id (X : Scheme.{u}) [IsAffine X] :
    affineComponentMap (𝟙 X) = 𝟙 (affineComponentSpace X) := by
  ext q
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
  rfl

private theorem component_map_comp {X Y Z : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsAffine Z] (f : Y ⟶ X) (g : Z ⟶ Y) :
    affineComponentMap (g ≫ f) = affineComponentMap g ≫ affineComponentMap f := by
  ext q
  obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe q
  rfl

private theorem over_pullbackId_left {C : Type*} [Category* C] [HasPullbacks C]
    {X : C} (E : Over X) :
    ((Over.pullbackId (X := X)).hom.app E).left = pullback.fst E.hom (𝟙 X) := by
  simp [Over.pullbackId, conjugateIsoEquiv,
    Over.mapPullbackAdj_counit_app]

private theorem over_pullbackComp_left {C : Type*} [Category* C] [HasPullbacks C]
    {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (E : Over X) :
    ((Over.pullbackComp g f).hom.app E).left ≫
      pullback.fst (pullback.snd E.hom f) g ≫ pullback.fst E.hom f =
        pullback.fst E.hom (g ≫ f) := by
  simp [Over.pullbackComp, conjugateIsoEquiv, Over.mapPullbackAdj_counit_app, Category.assoc]

private noncomputable def componentIdentity (X : Scheme.{u}) [IsAffine X]
    (E : Over (affineComponentSpace X)) :
    (Over.pullback (affineComponentMap (𝟙 X))).obj E ≅ E := by
  have h := component_map_id X
  have : IsIso (affineComponentMap (𝟙 X)) := h ▸ inferInstance
  refine Over.isoMk (asIso (pullback.fst E.hom (affineComponentMap (𝟙 X)))) ?_
  change pullback.fst E.hom (affineComponentMap (𝟙 X)) ≫ E.hom =
    pullback.snd E.hom (affineComponentMap (𝟙 X))
  rw [pullback.condition, h, Category.comp_id]

private theorem comparison_identity (X : Scheme.{u}) [IsAffine X]
    (E : Over (affineComponentSpace X)) :
    (comparisonIso (𝟙 X)).hom.app E ≫ (relativeComponentLift X).map
      (componentIdentity X E).hom =
        (Over.pullbackId (X := X)).hom.app ((relativeComponentLift X).obj E) := by
  apply Over.OverMorphism.ext
  apply lift_ext X
  · exact (Over.w _).trans (Over.w _).symm
  · intro z
    change relativeComponentCoordinate X E
      (((relativeComponentLift X).map (componentIdentity X E).hom).left
        ((comparisonHom (𝟙 X) E).left z)) = _
    erw [coordinate_map, comparisonHom_coordinate, comparisonCoordinate_fst]
    rw [over_pullbackId_left]
    rfl

private noncomputable def componentComposition {X Y Z : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsAffine Z] (f : Y ⟶ X) (g : Z ⟶ Y)
    (E : Over (affineComponentSpace X)) :
    (Over.pullback (affineComponentMap (g ≫ f))).obj E ≅
      (Over.pullback (affineComponentMap f) ⋙ Over.pullback (affineComponentMap g)).obj E :=
  Over.isoMk
    (pullback.congrHom rfl (component_map_comp f g) ≪≫
      (pullbackLeftPullbackSndIso E.hom (affineComponentMap f) (affineComponentMap g)).symm)
    (by simp)

private theorem componentComposition_fst {X Y Z : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsAffine Z] (f : Y ⟶ X) (g : Z ⟶ Y)
    (E : Over (affineComponentSpace X)) :
    (componentComposition f g E).hom.left ≫
      pullback.fst ((Over.pullback (affineComponentMap f)).obj E).hom (affineComponentMap g) ≫
      pullback.fst E.hom (affineComponentMap f) =
        pullback.fst E.hom (affineComponentMap (g ≫ f)) := by
  simp [componentComposition]

private theorem componentComposition_snd {X Y Z : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsAffine Z] (f : Y ⟶ X) (g : Z ⟶ Y)
    (E : Over (affineComponentSpace X)) :
    (componentComposition f g E).hom.left ≫
      pullback.snd ((Over.pullback (affineComponentMap f)).obj E).hom (affineComponentMap g) =
        pullback.snd E.hom (affineComponentMap (g ≫ f)) :=
  (componentComposition f g E).hom.w

private theorem comparisonIso_fst {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (E : Over (affineComponentSpace X))
    (z : ((relativeComponentLift X ⋙ Over.pullback f).obj E).left) :
    pullback.fst E.hom (affineComponentMap f)
        (relativeComponentCoordinate Y _ (((comparisonIso f).hom.app E).left z)) =
      relativeComponentCoordinate X E (pullback.fst ((relativeComponentLift X).obj E).hom f z) :=
  (congrArg (pullback.fst E.hom (affineComponentMap f))
    (comparisonHom_coordinate f E z)).trans (comparisonCoordinate_fst f E z)

private theorem pullback_map_fst {C : Type*} [Category* C] [HasPullbacks C]
    {X Y : C} (f : Y ⟶ X) {U V : Over X} (a : U ⟶ V) :
    ((Over.pullback f).map a).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ a.left := by
  simp [Over.pullback_map_left]

private theorem comparison_composition {X Y Z : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsAffine Z] (f : Y ⟶ X) (g : Z ⟶ Y)
    (E : Over (affineComponentSpace X)) :
    (comparisonIso (g ≫ f)).hom.app E ≫
        (relativeComponentLift Z).map (componentComposition f g E).hom =
      (Over.pullbackComp g f).hom.app ((relativeComponentLift X).obj E) ≫
        (Over.pullback g).map ((comparisonIso f).hom.app E) ≫
        (comparisonIso g).hom.app ((Over.pullback (affineComponentMap f)).obj E) := by
  let U := (relativeComponentLift X).obj E
  let E' := (Over.pullback (affineComponentMap f)).obj E
  let V := (relativeComponentLift Y).obj E'
  let t := ((Over.pullbackComp g f).hom.app U).left
  let v := ((Over.pullback g).map ((comparisonIso f).hom.app E)).left
  let w := ((comparisonIso g).hom.app E').left
  let m := ((relativeComponentLift Z).map (componentComposition f g E).hom).left
  let n := ((comparisonIso (g ≫ f)).hom.app E).left
  apply Over.OverMorphism.ext
  apply lift_ext Z
  · exact (Over.w _).trans (Over.w _).symm
  · intro z
    change relativeComponentCoordinate Z _ (m (n z)) =
      relativeComponentCoordinate Z _ (w (v (t z)))
    erw [coordinate_map]
    apply profinite_pullback_ext E'.hom (affineComponentMap g)
    · apply profinite_pullback_ext E.hom (affineComponentMap f)
      · have hl := ConcreteCategory.congr_hom (componentComposition_fst f g E)
          (relativeComponentCoordinate Z _ (n z))
        change pullback.fst E.hom (affineComponentMap f)
          (pullback.fst E'.hom (affineComponentMap g)
            ((componentComposition f g E).hom.left (relativeComponentCoordinate Z _ (n z)))) = _
        change pullback.fst E.hom (affineComponentMap f)
          (pullback.fst E'.hom (affineComponentMap g)
            ((componentComposition f g E).hom.left
              (relativeComponentCoordinate Z _ (n z)))) = _ at hl
        rw [hl]
        erw [comparisonIso_fst, comparisonIso_fst]
        have hv := congrArg
          (fun k : pullback (pullback.snd U.hom f) g ⟶ V.left ↦ k (t z))
          (pullback_map_fst g ((comparisonIso f).hom.app E))
        change _ = pullback.fst E.hom (affineComponentMap f)
          (relativeComponentCoordinate Y E' (pullback.fst V.hom g (v (t z))))
        change pullback.fst V.hom g (v (t z)) =
          ((comparisonIso f).hom.app E).left (pullback.fst (pullback.snd U.hom f) g (t z)) at hv
        rw [hv]
        erw [comparisonIso_fst]
        have ht := congrArg (fun k : pullback U.hom (g ≫ f) ⟶ U.left ↦ k z)
          (over_pullbackComp_left f g U)
        exact congrArg (relativeComponentCoordinate X E) ht.symm
      · have hl := ConcreteCategory.congr_hom
          (pullback.condition (f := E'.hom) (g := affineComponentMap g))
            ((componentComposition f g E).hom.left (relativeComponentCoordinate Z _ (n z)))
        have hs := ConcreteCategory.congr_hom (componentComposition_snd f g E)
          (relativeComponentCoordinate Z _ (n z))
        erw [coordinate_base Z ((Over.pullback (affineComponentMap (g ≫ f))).obj E)] at hs
        have hr := coordinate_base Z ((Over.pullback (affineComponentMap g)).obj E')
          (w (v (t z)))
        have hb : ((relativeComponentLift Z).obj
            ((Over.pullback (affineComponentMap (g ≫ f))).obj E)).hom (n z) =
          ((relativeComponentLift Z).obj ((Over.pullback (affineComponentMap g)).obj E')).hom
            (w (v (t z))) := congrArg (fun k ↦ k z)
          ((Over.w ((comparisonIso (g ≫ f)).hom.app E)).trans
            (Over.w ((Over.pullbackComp g f).hom.app U ≫
              (Over.pullback g).map ((comparisonIso f).hom.app E) ≫
                (comparisonIso g).hom.app E')).symm)
        have hp := ConcreteCategory.congr_hom
          (pullback.condition (f := E'.hom) (g := affineComponentMap g))
            (relativeComponentCoordinate Z _ (w (v (t z))))
        exact hl.trans ((congrArg (affineComponentMap g) hs).trans
          ((congrArg (fun a ↦ affineComponentMap g (ConnectedComponents.mk a)) hb).trans
            ((congrArg (affineComponentMap g) hr.symm).trans hp.symm)))
    · have hs := ConcreteCategory.congr_hom (componentComposition_snd f g E)
        (relativeComponentCoordinate Z _ (n z))
      erw [coordinate_base Z ((Over.pullback (affineComponentMap (g ≫ f))).obj E)] at hs
      have hr := coordinate_base Z ((Over.pullback (affineComponentMap g)).obj E')
        (w (v (t z)))
      have hb : ((relativeComponentLift Z).obj
          ((Over.pullback (affineComponentMap (g ≫ f))).obj E)).hom (n z) =
        ((relativeComponentLift Z).obj ((Over.pullback (affineComponentMap g)).obj E')).hom
          (w (v (t z))) := congrArg (fun k ↦ k z)
        ((Over.w ((comparisonIso (g ≫ f)).hom.app E)).trans
          (Over.w ((Over.pullbackComp g f).hom.app U ≫
            (Over.pullback g).map ((comparisonIso f).hom.app E) ≫
              (comparisonIso g).hom.app E')).symm)
      exact hs.trans ((congrArg ConnectedComponents.mk hb).trans hr.symm)

private theorem finite_components (T : Scheme.{u}) [IsAffine T]
    (F : Over (affineComponentSpace T) ⥤ T.ProEt)
    (p : ∀ E : Over (affineComponentSpace T), C((F.obj E).left, E.left))
    (hF : ∀ E : Over (affineComponentSpace T),
      (∀ x : (F.obj E).left, IsIso ((F.obj E).hom.stalkMap x)) ∧
      ∃ h : (F.obj E).left ≃ₜ
          {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ x, (h x).val.1 = (F.obj E).hom x) ∧ (∀ x, (h x).val.2 = p E x))
    (hp : ∀ (E : Over (affineComponentSpace T)) (x : (F.obj E).left),
      E.hom (p E x) = ConnectedComponents.mk ((F.obj E).hom x))
    (hmap : ∀ (W : Over T) (E : Over (affineComponentSpace T)) (g : C(W.left, E.left)),
      (∀ w : W.left, E.hom (g w) = ConnectedComponents.mk (W.hom w)) →
      ∃! m : W ⟶ (Scheme.ProEt.forget T).obj (F.obj E),
        ∀ w : W.left, p E (m.left w) = g w)
    (A C : FintypeCat.{u}) (q : affineComponentSpace T ⟶ FintypeCat.toProfinite.obj C)
    (f : A ⟶ C) :
    ∃ k : ∀ a : A, Over.mk (componentFiniteOpen T A C q f a).ι ⟶
        (Scheme.ProEt.forget T).obj (F.obj (componentFiniteStage A C q f)),
      (∀ (a : A) (w : (componentFiniteOpen T A C q f a).toScheme),
        pullback.snd q (FintypeCat.toProfinite.map f)
          (p (componentFiniteStage A C q f) ((k a).left w)) = a) ∧
      (∀ a : A, IsOpenImmersion (k a).left) ∧
      Nonempty (IsColimit (Cofan.mk
        ((Scheme.ProEt.forget T).obj (F.obj (componentFiniteStage A C q f))) k)) ∧
      ∀ a : A, Set.range (k a).left =
        {x | pullback.snd q (FintypeCat.toProfinite.map f)
          (p (componentFiniteStage A C q f) x) = a} := by
  classical
  let E := componentFiniteStage A C q f
  let U (a : A) := componentFiniteOpen T A C q f a
  let e : E.left ≅ CompHausLike.pullback q (FintypeCat.toProfinite.map f) :=
    (pullback.isLimit q (FintypeCat.toProfinite.map f)).conePointUniqueUpToIso
      (CompHausLike.pullback.isLimit q (FintypeCat.toProfinite.map f))
  let eh := CompHausLike.homeoOfIso e
  have efst (x : E.left) : (eh x).val.1 = E.hom x :=
    by
      exact ConcreteCategory.congr_hom
        ((pullback.isLimit q (FintypeCat.toProfinite.map f)).conePointUniqueUpToIso_hom_comp
          (CompHausLike.pullback.isLimit q (FintypeCat.toProfinite.map f)) WalkingCospan.left) x
  have esnd (x : E.left) : (eh x).val.2 =
      pullback.snd q (FintypeCat.toProfinite.map f) x := by
    exact ConcreteCategory.congr_hom
      ((pullback.isLimit q (FintypeCat.toProfinite.map f)).conePointUniqueUpToIso_hom_comp
        (CompHausLike.pullback.isLimit q (FintypeCat.toProfinite.map f)) WalkingCospan.right) x
  let g (a : A) : C((U a).toScheme, E.left) :=
    ⟨fun t ↦ eh.symm ⟨(ConnectedComponents.mk t.val, a), t.property⟩,
      eh.symm.continuous.comp
        ((ConnectedComponents.continuous_coe.comp continuous_subtype_val).prodMk
          continuous_const |>.subtype_mk _)⟩
  have hg (a : A) (w : (U a).toScheme) : E.hom (g a w) =
      ConnectedComponents.mk ((U a).ι w) := by
    erw [← efst]
    exact congrArg (fun z ↦ z.val.1) (eh.apply_symm_apply _)
  let k (a : A) : Over.mk (U a).ι ⟶ (Scheme.ProEt.forget T).obj (F.obj E) :=
    (hmap (Over.mk (U a).ι) E (g a) (hg a)).choose
  have hk (a : A) (w : (U a).toScheme) : p E ((k a).left w) = g a w :=
    (hmap (Over.mk (U a).ι) E (g a) (hg a)).choose_spec.1 w
  let r : C((F.obj E).left, FintypeCat.toProfinite.obj A) :=
    ⟨fun x ↦ (eh (p E x)).val.2,
      continuous_snd.comp (continuous_subtype_val.comp (eh.continuous.comp (p E).continuous))⟩
  have hkr (a : A) (w : (U a).toScheme) : r ((k a).left w) = a := by
    change (eh (p E ((k a).left w))).val.2 = a
    erw [hk]
    exact congrArg (fun z ↦ z.val.2) (eh.apply_symm_apply _)
  have hrange (a : A) : Set.range (k a).left = r ⁻¹' {a} := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact hkr a w
    · intro hx
      have hx' : q (ConnectedComponents.mk ((F.obj E).hom x)) = f a := by
        erw [← hp E x, ← efst]
        exact (eh (p E x)).property.trans (congrArg f hx)
      let w : (U a).toScheme := ⟨(F.obj E).hom x, hx'⟩
      refine ⟨w, ?_⟩
      obtain ⟨h, ht, hpt⟩ := (hF E).2
      apply h.injective
      apply Subtype.ext
      apply Prod.ext
      · erw [ht, ht]
        exact congrArg (fun l : (U a).toScheme ⟶ T ↦ l w) (k a).w
      · erw [hpt, hpt, hk]
        apply eh.injective
        erw [show eh (g a w) = ⟨(ConnectedComponents.mk w.val, a), w.property⟩ from
          eh.apply_symm_apply _]
        apply Subtype.ext
        exact Prod.ext ((efst _).trans (hp E x)).symm hx.symm
  have hki (a : A) : IsOpenImmersion (k a).left := by
    have hemb : IsEmbedding (k a).left := IsEmbedding.of_comp
      (k a).left.continuous (F.obj E).hom.continuous (by
        have heq : (fun w : (U a).toScheme ↦ (F.obj E).hom ((k a).left w)) =
            (fun w : (U a).toScheme ↦ (U a).ι w) := by
          funext w
          exact congrArg (fun l : (U a).toScheme ⟶ T ↦ l w) (k a).w
        exact (congrArg (fun l : (U a).toScheme → T ↦ IsEmbedding l) heq).mpr
          (U a).ι.isOpenEmbedding.isEmbedding)
    have hopen : IsOpenEmbedding (k a).left :=
      ⟨hemb, (hrange a).symm ▸
        (isOpen_discrete ({a} : Set (FintypeCat.toProfinite.obj A))).preimage r.continuous⟩
    have (w : (U a).toScheme) : IsIso ((k a).left.stalkMap w) := by
      have := (hF E).1 ((k a).left w)
      have hc : IsIso (((k a).left ≫ (F.obj E).hom).stalkMap w) := by
        have hw : (k a).left ≫ (F.obj E).hom = (U a).ι := (k a).w
        exact (congrArg (fun l : (U a).toScheme ⟶ T ↦ IsIso (l.stalkMap w)) hw).mpr
          (inferInstance : IsIso ((U a).ι.stalkMap w))
      have : IsIso ((F.obj E).hom.stalkMap ((k a).left w) ≫ (k a).left.stalkMap w) := by
        erw [← Scheme.Hom.stalkMap_comp]
        exact hc
      exact IsIso.of_isIso_comp_left ((F.obj E).hom.stalkMap ((k a).left w)) _
    exact IsOpenImmersion.of_isIso_stalkMap _ hopen
  have (a : A) := hki a
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (fun a ↦ (k a).left) (by
      apply top_unique
      intro x hx
      have hx' : x ∈ (k (r x)).left.opensRange := by
        change x ∈ Set.range (k (r x)).left
        erw [hrange]
        rfl
      exact (le_iSup (fun a ↦ (k a).left.opensRange) (r x)) hx') (by
      intro a b hab
      apply disjoint_iff_inf_le.mpr
      intro x hx
      obtain ⟨y, hy⟩ := hx.1
      obtain ⟨z, hz⟩ := hx.2
      exact hab ((hkr a y).symm.trans ((congrArg r (hy.trans hz.symm)).trans (hkr b z))))
  let hcOver : IsColimit (Cofan.mk ((Scheme.ProEt.forget T).obj (F.obj E)) k) :=
    isColimitOfIsColimitCofanMkObj (Over.forget T) (fun a ↦ Over.mk (U a).ι) k hc
  refine ⟨k, ?_, hki, ⟨hcOver⟩, ?_⟩
  · intro a w
    change pullback.snd q (FintypeCat.toProfinite.map f) (p E ((k a).left w)) = a
    rw [← esnd]
    exact hkr a w
  · intro a
    ext x
    rw [hrange]
    change (eh (p E x)).val.2 = a ↔ _
    rw [esnd]
    rfl

private theorem pullback_map_open {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U V : Over X} (j : U ⟶ V) [IsOpenImmersion j.left] :
    IsOpenImmersion (((Over.pullback f).map j).left) := by
  have he : ((Over.pullback f).map j).left =
      pullback.map U.hom f V.hom f j.left (𝟙 Y) (𝟙 X)
        (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  rw [he]
  infer_instance

private theorem range_pullback_map {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U V : Over X} (j : U ⟶ V) :
    Set.range (((Over.pullback f).map j).left) =
      pullback.fst V.hom f ⁻¹' Set.range j.left := by
  have he : ((Over.pullback f).map j).left =
      pullback.map U.hom f V.hom f j.left (𝟙 Y) (𝟙 X)
        (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  rw [he]
  have h := Scheme.Pullback.range_map (f := U.hom) (g := f) V.hom f j.left
    (𝟙 Y) (𝟙 X) (by simp) (by simp)
  simpa using h

private theorem iso_hom_inv_apply {Y : Scheme.{u}} {U V : Over Y}
    (e : U ≅ V) (z : V.left) : e.hom.left (e.inv.left z) = z := by
  have h := congrArg (fun k ↦ k.left) e.inv_hom_id
  exact congrArg (fun k : V.left ⟶ V.left ↦ k z) h

private theorem iso_inv_hom_apply {Y : Scheme.{u}} {U V : Over Y}
    (e : U ≅ V) (z : U.left) : e.inv.left (e.hom.left z) = z := by
  have h := congrArg (fun k ↦ k.left) e.hom_inv_id
  exact congrArg (fun k : U.left ⟶ U.left ↦ k z) h

private theorem range_comp_iso {Y : Scheme.{u}} {U V W : Over Y}
    (a : U ⟶ V) (e : V ≅ W) :
    Set.range (a ≫ e.hom).left = e.inv.left ⁻¹' Set.range a.left := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (iso_inv_hom_apply e (a.left w)).symm⟩
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    exact (congrArg e.hom.left hw).trans (iso_hom_inv_apply e z)

private theorem comparison_finite (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (A C : FintypeCat.{u})
    (q : affineComponentSpace X ⟶ FintypeCat.toProfinite.obj C) (r : A ⟶ C) :
    ∃ j : ∀ a : A,
        Over.mk (componentFiniteOpen X A C q r a).ι ⟶
          (relativeComponentLift X).obj (componentFiniteStage A C q r),
      (∀ (a : A) (x : (componentFiniteOpen X A C q r a).toScheme),
        pullback.snd q (FintypeCat.toProfinite.map r)
          (relativeComponentCoordinate X (componentFiniteStage A C q r)
            ((j a).left x)) = a) ∧
      (∀ a : A, IsOpenImmersion (j a).left) ∧
      Nonempty (IsColimit (Cofan.mk
        ((relativeComponentLift X).obj (componentFiniteStage A C q r)) j)) ∧
      (∀ a : A, IsOpenImmersion
        (((Over.pullback f).map (j a) ≫
          (comparisonIso f).hom.app (componentFiniteStage A C q r)).left)) ∧
      (∀ a : A,
        Set.range (((Over.pullback f).map (j a) ≫
          (comparisonIso f).hom.app (componentFiniteStage A C q r)).left) =
          (((Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj
            (componentFiniteStage A C q r)).hom) ⁻¹'
              (componentFiniteOpen Y A C (affineComponentMap f ≫ q) r a).carrier ∩
            {z | pullback.snd q (FintypeCat.toProfinite.map r)
              (pullback.fst (componentFiniteStage A C q r).hom (affineComponentMap f)
                (relativeComponentCoordinate Y
                  ((Over.pullback (affineComponentMap f)).obj (componentFiniteStage A C q r))
                  z)) = a}) ∧
      Nonempty (IsColimit (Cofan.mk
        ((Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj
          (componentFiniteStage A C q r))
        (fun a : A ↦ (Over.pullback f).map (j a) ≫
          (comparisonIso f).hom.app (componentFiniteStage A C q r)))) := by
  classical
  obtain ⟨θ, hθ, H, hH, _, hst, _, _⟩ := relative_component_lift_pullback_space X
  let F := (component_relative_profinite_site X).choose
  let p := relativeComponentCoordinate X
  have hgeom : ∀ E : Over (affineComponentSpace X),
      (∀ x : (F.obj E).left, IsIso ((F.obj E).hom.stalkMap x)) ∧
      ∃ h : (F.obj E).left ≃ₜ
          {z : X × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ x, (h x).val.1 = (F.obj E).hom x) ∧ (∀ x, (h x).val.2 = p E x) :=
    fun E ↦ ⟨hst E, H E, fun x ↦ (hH E x).1, fun x ↦ (hH E x).2⟩
  obtain ⟨j, hj, hjo, hjc, hjr⟩ := finite_components X F p hgeom
    (coordinate_base X) ((component_relative_profinite_site X).choose_spec.2.1.choose_spec.2.2)
    A C q r
  let E := componentFiniteStage A C q r
  let B := (Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj E
  let k (a : A) := (Over.pullback f).map (j a) ≫ (comparisonIso f).hom.app E
  let label (z : B.left) := pullback.snd q (FintypeCat.toProfinite.map r)
    (pullback.fst E.hom (affineComponentMap f) (relativeComponentCoordinate Y _ z))
  have hlabel (z : ((relativeComponentLift X ⋙ Over.pullback f).obj E).left) :
      label (((comparisonIso f).hom.app E).left z) =
        pullback.snd q (FintypeCat.toProfinite.map r)
          (relativeComponentCoordinate X E
            (pullback.fst ((relativeComponentLift X).obj E).hom f z)) := by
    dsimp only [label]
    erw [comparisonHom_coordinate, comparisonCoordinate_fst]
  have hlabel_base (z : B.left) (a : A) (hz : label z = a) :
      B.hom z ∈ (componentFiniteOpen Y A C (affineComponentMap f ≫ q) r a).carrier := by
    change (affineComponentMap f ≫ q) (ConnectedComponents.mk (B.hom z)) = r a
    have hbase := coordinate_base Y ((Over.pullback (affineComponentMap f)).obj E) z
    have hp := ConcreteCategory.congr_hom
      (pullback.condition (f := E.hom) (g := affineComponentMap f))
        (relativeComponentCoordinate Y _ z)
    have hq := ConcreteCategory.congr_hom
      (pullback.condition (f := q) (g := FintypeCat.toProfinite.map r))
        (pullback.fst E.hom (affineComponentMap f) (relativeComponentCoordinate Y _ z))
    exact (congrArg (fun t ↦ (affineComponentMap f ≫ q) t) hbase.symm).trans
      ((congrArg (fun t ↦ q t) hp.symm).trans (hq.trans (congrArg (fun b ↦ r b) hz)))
  have hkr (a : A) : Set.range (k a).left = {z | label z = a} := by
    ext z
    let e := (comparisonIso f).app E
    have he : Set.range (k a).left =
        e.inv.left ⁻¹' Set.range (((Over.pullback f).map (j a)).left) :=
      range_comp_iso ((Over.pullback f).map (j a)) e
    rw [he, range_pullback_map, hjr]
    change _ ↔ label z = a
    have h := hlabel (e.inv.left z)
    have hi : ((comparisonIso f).hom.app E).left (e.inv.left z) = z :=
      iso_hom_inv_apply e z
    rw [hi] at h
    change pullback.snd q (FintypeCat.toProfinite.map r)
      (relativeComponentCoordinate X E (pullback.fst ((relativeComponentLift X).obj E).hom f
        (e.inv.left z))) = a ↔ label z = a
    rw [← h]
  have hko (a : A) : IsOpenImmersion (k a).left := by
    have := hjo a
    have := pullback_map_open f (j a)
    change IsOpenImmersion
      ((((Over.pullback f).map (j a)).left) ≫ ((comparisonIso f).hom.app E).left)
    infer_instance
  have (a : A) := hko a
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (fun a ↦ (k a).left) (by
      apply top_unique
      intro z hz
      have hz' : z ∈ (k (label z)).left.opensRange := by
        change z ∈ Set.range (k (label z)).left
        rw [hkr]
        rfl
      exact (le_iSup (fun a ↦ (k a).left.opensRange) (label z)) hz') (by
      intro a b hab
      apply disjoint_iff_inf_le.mpr
      intro z hz
      have hza : label z = a := by
        have : z ∈ Set.range (k a).left := hz.1
        rwa [hkr] at this
      have hzb : label z = b := by
        have : z ∈ Set.range (k b).left := hz.2
        rwa [hkr] at this
      exact hab (hza.symm.trans hzb))
  refine ⟨j, hj, hjo, hjc, hko, ?_, ?_⟩
  · intro a
    rw [hkr]
    ext z
    exact ⟨fun hz ↦ ⟨hlabel_base z a hz, hz⟩, fun hz ↦ hz.2⟩
  · exact ⟨isColimitOfIsColimitCofanMkObj (Over.forget Y) _ k hc⟩

end

set_option backward.isDefEq.respectTransparency false in
/-- The two affine base-change functors are canonically naturally isomorphic, with
projection, identity, composition, finite-clopen, and all finite-presentation normalizations.

Source: Hemo--Richarz--Scholbach, construction preceding (4.1), pp. 8--9 and Corollary
4.4(2); Bhatt--Scholze, Lemma 2.2.8 and its more precise statement
(blueprint: lem-zl-component-lift-base-change).

Proof for stage 3.
1. Use the geometric description of the relative lift
   (`lem-sfb-relative-component-lift-pullback-space`) to identify its points with pairs
   over the connected-component quotient, and its structure maps as stalkwise
   isomorphisms. The continuous map (y,(q,s)) to (f(y),s) lifts uniquely to a scheme
   map by `new-lem-zl-stalk-isomorphism-lifting`. The fibre-product property
   (`def-pc-fibre-product`) gives a map from the Y-lift to the scheme pullback.
2. Conversely the two projections of that scheme pullback give the continuous map
   z to (y,(kappa_Y(y),s)) into the Y-lift. Lift uniquely along its stalkwise
   isomorphism to Y. This is the forward comparison, preserving Y and E coordinates.
3. Both composites preserve these coordinates. Uniqueness of continuous lifting and
   the scheme pullback property make them identities. The same argument shows that
   any map into a lift is determined by its base map and profinite coordinate.
4. Apply this uniqueness to every map E to E', giving naturality without finite-stage
   factorization. Apply it to the identity and to g followed by f, giving precisely
   the slice identity and associativity equations displayed below.
5. At a finite clopen stage, the actual restricted opens form the coproduct from
   `lem-zl-component-relative-profinite-site`. Pulling them back uses
   `lem-weil-pbc-open-fibre-product`; base change preserves their finite coproduct by
   `lem-sc-etale-fibre-product-base-change-coproduct`. Their labels determine the
   comparison, including repeated and empty blocks: the image of block a is the part of the
   pulled-back open of Y whose finite coordinate is a (several blocks may share one open).
   Finally naturality applied to every leg of every cofiltered finite-stage presentation
   gives the cone equations.
   The pulled-back profinite cone is limiting, as compatible pairs (q,s_i) correspond
   uniquely and continuously to (q,s). The relative-lift characterization gives the
   limiting cone on the right; the comparison transports it to the left. -/
theorem component_lift_base_change :
    ∃ c : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
        relativeComponentLift X ⋙ Over.pullback f ≅
          Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y,
      (∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
        (E : Over (affineComponentSpace X))
        (z : ((relativeComponentLift X ⋙ Over.pullback f).obj E).left),
        pullback.fst E.hom (affineComponentMap f)
            (relativeComponentCoordinate Y ((Over.pullback (affineComponentMap f)).obj E)
              (((c f).hom.app E).left z)) =
          relativeComponentCoordinate X E
            (pullback.fst ((relativeComponentLift X).obj E).hom f z)) ∧
      (∀ (X : Scheme.{u}) [IsAffine X] (E : Over (affineComponentSpace X)),
        ∃ e : (Over.pullback (affineComponentMap (𝟙 X))).obj E ≅ E,
          e.hom.left = pullback.fst E.hom (affineComponentMap (𝟙 X)) ∧
          (c (𝟙 X)).hom.app E ≫ (relativeComponentLift X).map e.hom =
            (Over.pullbackId (X := X)).hom.app ((relativeComponentLift X).obj E)) ∧
      (∀ (X Y Z : Scheme.{u}) [IsAffine X] [IsAffine Y] [IsAffine Z]
        (f : Y ⟶ X) (g : Z ⟶ Y) (E : Over (affineComponentSpace X)),
        ∃ e : (Over.pullback (affineComponentMap (g ≫ f))).obj E ≅
            (Over.pullback (affineComponentMap f) ⋙
              Over.pullback (affineComponentMap g)).obj E,
          e.hom.left ≫
              pullback.fst ((Over.pullback (affineComponentMap f)).obj E).hom
                (affineComponentMap g) ≫ pullback.fst E.hom (affineComponentMap f) =
            pullback.fst E.hom (affineComponentMap (g ≫ f)) ∧
          e.hom.left ≫
              pullback.snd ((Over.pullback (affineComponentMap f)).obj E).hom
                (affineComponentMap g) =
            pullback.snd E.hom (affineComponentMap (g ≫ f)) ∧
          (c (g ≫ f)).hom.app E ≫ (relativeComponentLift Z).map e.hom =
            (Over.pullbackComp g f).hom.app ((relativeComponentLift X).obj E) ≫
              (Over.pullback g).map ((c f).hom.app E) ≫
                (c g).hom.app ((Over.pullback (affineComponentMap f)).obj E)) ∧
      (∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
        (A C : FintypeCat.{u})
        (q : affineComponentSpace X ⟶ FintypeCat.toProfinite.obj C) (r : A ⟶ C),
        Function.Surjective q →
        ∃ j : ∀ a : A,
            Over.mk (componentFiniteOpen X A C q r a).ι ⟶
              (relativeComponentLift X).obj (componentFiniteStage A C q r),
          (∀ (a : A) (x : (componentFiniteOpen X A C q r a).toScheme),
            pullback.snd q (FintypeCat.toProfinite.map r)
              (relativeComponentCoordinate X (componentFiniteStage A C q r)
                ((j a).left x)) = a) ∧
          (∀ a : A, IsOpenImmersion (j a).left) ∧
          Nonempty (IsColimit (Cofan.mk
            ((relativeComponentLift X).obj (componentFiniteStage A C q r)) j)) ∧
          (∀ a : A, IsOpenImmersion
            (((Over.pullback f).map (j a) ≫
              (c f).hom.app (componentFiniteStage A C q r)).left)) ∧
          (∀ a : A,
            Set.range (((Over.pullback f).map (j a) ≫
              (c f).hom.app (componentFiniteStage A C q r)).left) =
              (((Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj
                (componentFiniteStage A C q r)).hom) ⁻¹'
                  (componentFiniteOpen Y A C (affineComponentMap f ≫ q) r a).carrier ∩
                {z | pullback.snd q (FintypeCat.toProfinite.map r)
                  (pullback.fst (componentFiniteStage A C q r).hom (affineComponentMap f)
                    (relativeComponentCoordinate Y
                      ((Over.pullback (affineComponentMap f)).obj (componentFiniteStage A C q r))
                      z)) = a}) ∧
          Nonempty (IsColimit (Cofan.mk
            ((Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).obj
              (componentFiniteStage A C q r))
            (fun a : A ↦ (Over.pullback f).map (j a) ≫
              (c f).hom.app (componentFiniteStage A C q r))))) ∧
      (∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
        (I : Type u) [SmallCategory I] [IsCofiltered I]
        (D : I ⥤ Over (affineComponentSpace X)) (s : Cone D),
        (∀ i : I, IsComponentFiniteStage (D.obj i)) → IsLimit s →
        Nonempty (IsLimit ((relativeComponentLift X ⋙ Over.pullback f).mapCone s)) ∧
          Nonempty (IsLimit ((Over.pullback (affineComponentMap f) ⋙
            relativeComponentLift Y).mapCone s)) ∧
          ∀ i : I,
            (relativeComponentLift X ⋙ Over.pullback f).map (s.π.app i) ≫
                (c f).hom.app (D.obj i) =
              (c f).hom.app s.pt ≫
                (Over.pullback (affineComponentMap f) ⋙ relativeComponentLift Y).map
                  (s.π.app i)) := by
  classical
  refine ⟨fun {_ _} _ _ f ↦ comparisonIso f, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y _ _ f E z
    exact (congrArg (pullback.fst E.hom (affineComponentMap f))
      (comparisonHom_coordinate f E z)).trans (comparisonCoordinate_fst f E z)
  · intro X _ E
    exact ⟨componentIdentity X E, rfl, comparison_identity X E⟩
  · intro X Y Z _ _ _ f g E
    exact ⟨componentComposition f g E, componentComposition_fst f g E,
      componentComposition_snd f g E, comparison_composition f g E⟩
  · intro X Y _ _ f A C q r _
    exact comparison_finite X Y f A C q r
  · intro X Y _ _ f I _ _ D s hstage hs
    have hx : IsLimit ((relativeComponentLift X).mapCone s) :=
      ((component_relative_profinite_site X).choose_spec.2.2.2.2.1 I D s hstage hs).some
    have hl : IsLimit ((relativeComponentLift X ⋙ Over.pullback f).mapCone s) :=
      isLimitOfPreserves (Over.pullback f) hx
    exact ⟨⟨hl⟩, ⟨IsLimit.mapConeEquiv (comparisonIso f) hl⟩,
      fun i ↦ (comparisonIso f).hom.naturality (s.π.app i)⟩

end AlgebraicGeometry.ProEtale
