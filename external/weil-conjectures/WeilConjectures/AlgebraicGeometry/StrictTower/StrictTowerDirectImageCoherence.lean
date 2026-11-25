/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Unit, associativity and mate pasting for strict-tower direct image

Source: Stacks Project, Tags 0D6D and 07A7. These equations concern the canonical
operations and do not assert any compactification comparison or its invertibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The normalized compositor is uniquely determined by canonical adjunction conjugation.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: lem-cbc-strict-tower-direct-image-coherence).
Proof: take the displayed conjugate; equality to it also proves uniqueness. -/
theorem rCompEq_existsUnique {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    ∃! e : R B f ⋙ R B g ≅ R B h,
      e = conjugateIsoEquiv ((adj B g).comp (adj B f)) (adj B h)
        (eqToIso (congrArg (G B) w.symm) ≪≫ gComp B f g) := by
  exact ⟨_, rfl, fun _ he ↦ he⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Direct-image composition with a supplied equation for the composite.
The determining theorem fixes its data by equality to the canonical conjugate.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: lem-cbc-strict-tower-direct-image-coherence). -/
def rCompEq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) : R B f ⋙ R B g ≅ R B h :=
  Classical.choose (rCompEq_existsUnique B f g h w)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- This representative is exactly the canonical conjugate compositor.
Source: Stacks, Tag 07A7 (blueprint: lem-cbc-strict-tower-direct-image-coherence).
Proof: apply the specification of its uniquely determining choice. -/
theorem rCompEq_spec {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : f ≫ g = h) :
    rCompEq B f g h w =
      conjugateIsoEquiv ((adj B g).comp (adj B f)) (adj B h)
        (eqToIso (congrArg (G B) w.symm) ≪≫ gComp B f g) :=
  (Classical.choose_spec (rCompEq_existsUnique B f g h w)).1

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Equality transport agrees with the standard equality isomorphism.
Source: equality elimination (blueprint: lem-cbc-strict-tower-direct-image-coherence). -/
theorem rCompEq_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : f ≫ g = h) :
    rCompEq B f g h w = rComp B f g ≪≫ eqToIso (congrArg (R B) w) := by
  subst h
  simp only [rCompEq_spec, eqToIso_refl, Iso.refl_trans, Iso.trans_refl]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem directImage_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) (A : Type (u + 1)) [CommRing A]
    (N : Modules A X) (U : Y.ProEt)
    (m : ((moduleDirectImage A f).obj N).val.obj (Opposite.op U)) :
    ((eqToIso (congrArg (moduleDirectImage A) e)).hom.app N).val.app
        (Opposite.op U) m =
      N.val.map (eqToHom (congrArg (fun t ↦ (Scheme.proEtaleBaseChange t).obj U) e.symm)).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pasting_transport
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (e : fg = f ≫ g) (U : P.Over Q Z) :
    (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g fg e).hom.app U =
      eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U) e) ≫
        (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g).hom.app U := by
  cases e
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem site_pasting
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y Z W : C} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X) (U : P.Over Q X) :
    (MorphismProperty.Over.pullbackComp j (h ≫ k)).hom.app U ≫
        (MorphismProperty.Over.pullback P Q j).map
          ((MorphismProperty.Over.pullbackComp h k).hom.app U) =
      eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U)
        (Category.assoc j h k).symm) ≫
        (MorphismProperty.Over.pullbackComp (j ≫ h) k).hom.app U ≫
        (MorphismProperty.Over.pullbackComp j h).hom.app
          ((MorphismProperty.Over.pullback P Q k).obj U) := by
  have hp := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_assoc (P := P) (Q := Q) j h k)) U
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hp
  rw [pasting_transport (j ≫ h) k (j ≫ h ≫ k) (Category.assoc j h k).symm U] at hp
  simpa only [Category.assoc] using hp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem directComp_hom_apply
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type (u + 1)) [CommRing A]
    (N : Modules A Z) (U : V.ProEt)
    (m : ((moduleDirectImage A h ⋙
      moduleDirectImage A k).obj N).val.obj (Opposite.op U)) :
    ((moduleRComp A h k).hom.app N).val.app (Opposite.op U) m =
      N.val.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U).op m := by
  exact (Classical.choose_spec (moduleRComp_existsUnique A h k)).1 N U m

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem directImage_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1)) [CommRing A]
    {N N' : Modules A X} (a : N ⟶ N') (U : Y.ProEt)
    (m : ((moduleDirectImage A f).obj N).val.obj (Opposite.op U)) :
    (((moduleDirectImage A f).map a).val.app (Opposite.op U)) m =
      a.val.app (Opposite.op ((Scheme.proEtaleBaseChange f).obj U)) m := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem directImage_obj_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1)) [CommRing A]
    (N : Modules A X)
    {U V : Y.ProEt} (a : U ⟶ V)
    (m : ((moduleDirectImage A f).obj N).val.obj (Opposite.op V)) :
    (((moduleDirectImage A f).obj N).val.map a.op) m =
      N.val.map ((Scheme.proEtaleBaseChange f).map a).op m := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem restriction_pasting
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat} (N : PresheafOfModules R)
    {U V T U' V' : C} (a : U ⟶ V) (b : V ⟶ T)
    (c : U ⟶ U') (d : U' ⟶ V') (e : V' ⟶ T)
    (h : a ≫ b = c ≫ d ≫ e) (m : N.obj (Opposite.op T)) :
    N.map a.op (N.map b.op m) = N.map c.op (N.map d.op (N.map e.op m)) := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp]
  rw [h, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem directImage_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    Functor.isoWhiskerLeft (moduleDirectImage A j) (moduleRComp A h k) ≪≫
        (moduleRComp A j (h ≫ k)) =
      (Functor.associator (moduleDirectImage A j)
          (moduleDirectImage A h)
          (moduleDirectImage A k)).symm ≪≫
        Functor.isoWhiskerRight (moduleRComp A j h)
          (moduleDirectImage A k) ≪≫
        (moduleRComp A (j ≫ h) k) ≪≫
        eqToIso (congrArg (moduleDirectImage A) (Category.assoc j h k)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  ext m
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [directImage_map_apply k A ((moduleRComp A j h).hom.app N) U]
  erw [directComp_hom_apply j h A N ((Scheme.proEtaleBaseChange k).obj U)]
  erw [directComp_hom_apply (j ≫ h) k A N U]
  conv_rhs => erw [directImage_transport (Category.assoc j h k) A N U]
  conv_lhs => erw [directComp_hom_apply h k A
    ((moduleDirectImage A j).obj N) U m]
  conv_lhs => erw [directComp_hom_apply j (h ≫ k) A N U]
  conv_lhs => erw [directImage_obj_map_apply j A N
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U)]
  exact restriction_pasting N.val _ _ _ _ _
    (site_pasting (P := @WeaklyEtale) (Q := ⊤) j h k U) m

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def moduleAdj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] : modulePullback A f ⊣ moduleDirectImage A f :=
  Scheme.proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
    (constantRingIso A f)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mate_transport
    {C D E I : Type*} [Category C] [Category D] [Category E]
    (L : I → C ⥤ E) (R : I → E ⥤ C) (adj : ∀ i, L i ⊣ R i)
    {F : C ⥤ D} {G : D ⥤ E} {F' : D ⥤ C} {G' : E ⥤ D}
    (aF : F ⊣ F') (aG : G ⊣ G') {i i' : I} (e : i = i')
    (d : G' ⋙ F' ≅ R i) :
    Adjunction.leftAdjointCompIso aF aG (adj i')
        (d ≪≫ eqToIso (congrArg R e)) =
      Adjunction.leftAdjointCompIso aF aG (adj i) d ≪≫ eqToIso (congrArg L e) := by
  cases e
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] (M : Modules A X) :
    (moduleGComp A j (h ≫ k)).hom.app M ≫
        (modulePullback A j).map ((moduleGComp A h k).hom.app M) =
      (eqToIso (congrArg (modulePullback A)
        (Category.assoc j h k).symm)).hom.app M ≫
        (moduleGComp A (j ≫ h) k).hom.app M ≫
        (moduleGComp A j h).hom.app ((modulePullback A k).obj M) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (moduleAdj k A) (moduleAdj h A) (moduleAdj j A)
    (moduleAdj (h ≫ k) A) (moduleAdj (j ≫ h) A)
    (moduleAdj (j ≫ h ≫ k) A)
    (moduleRComp A h k) (moduleRComp A j h)
    ((moduleRComp A (j ≫ h) k) ≪≫
      eqToIso (congrArg (moduleDirectImage A) (Category.assoc j h k)))
    (moduleRComp A j (h ≫ k)) (directImage_coherence j h k A)
  have ht := mate_transport (modulePullback A)
    (moduleDirectImage A) (fun f ↦ moduleAdj f A)
    (moduleAdj k A) (moduleAdj (j ≫ h) A) (Category.assoc j h k)
    (moduleRComp A (j ≫ h) k)
  rw [ht] at hh
  have hi := NatTrans.congr_app (congrArg Iso.inv hh) M
  simpa only [moduleGComp, moduleAdj, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id, Category.assoc, eqToIso.inv, eqToIso.hom]
    using hi.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem towerGComp_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type (u + 1)) [CommRing A] (M : Towers A Z) (n : ℕᵒᵖ) :
    ((towerGComp A f g).hom.app M).app n =
      (moduleGComp A f g).hom.app (M.obj n) := by
  change (moduleGComp A f g).hom.app (M.obj n) ≫ 𝟙 _ = _
  exact Category.comp_id _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tower_map_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] {M N : Towers A Y} (a : M ⟶ N) (n : ℕᵒᵖ) :
    ((towerPullback A f).map a).app n = (modulePullback A f).map (a.app n) := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tower_coherence {X Y Z W : Scheme.{u}}
    (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X) (A : Type (u + 1)) [CommRing A] :
    towerGComp A j (h ≫ k) ≪≫
        Functor.isoWhiskerRight (towerGComp A h k) (towerPullback A j) =
      eqToIso (congrArg (towerPullback A) (Category.assoc j h k).symm) ≪≫
        towerGComp A (j ≫ h) k ≪≫
        Functor.isoWhiskerLeft (towerPullback A k) (towerGComp A j h) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    towerGComp_app, tower_map_app]
  exact ordinary_coherence j h k A (M.obj n)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem descend_coherence
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B)
    (F02 : C ⥤ E) (F13 : D ⥤ B) (F03 F03' : C ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [F02.Additive] [F13.Additive]
    [F03.Additive] [F03'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F02] [PreservesFiniteColimits F02]
    [PreservesFiniteLimits F13] [PreservesFiniteColimits F13]
    [PreservesFiniteLimits F03] [PreservesFiniteColimits F03]
    [PreservesFiniteLimits F03'] [PreservesFiniteColimits F03']
    (a02 : F02 ≅ F ⋙ G) (a13 : F13 ≅ G ⋙ H)
    (a0 : F03 ≅ F02 ⋙ H) (a1 : F03' ≅ F ⋙ F13) (e : F03 ≅ F03')
    (ho : a0 ≪≫ Functor.isoWhiskerRight a02 H =
      e ≪≫ a1 ≪≫ Functor.isoWhiskerLeft F a13) :
    (Functor.mapDerivedCategoryNatIso a0).hom ≫
        (Functor.mapDerivedCategoryCompIso F02 H).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso a02).hom
          H.mapDerivedCategory ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompIso F G).inv
          H.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso e).hom ≫
        (Functor.mapDerivedCategoryNatIso a1).hom ≫
        (Functor.mapDerivedCategoryCompIso F F13).inv ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryNatIso a13).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryCompIso G H).inv := by
  have hd := congrArg (fun t ↦ (Functor.mapDerivedCategoryNatIso t).hom) ho
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hd
  have hR := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a02 H
  have hL := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F a13
  have hC := Functor.mapDerivedCategoryCompIso_assoc F G H
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F02 H).inv,
    ← hR, Category.assoc, ← hC]
  have ht := congrArg (fun t ↦ t ≫
    (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).inv ≫
    Functor.whiskerLeft F.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso G H).inv) hd
  calc
    _ = ((Functor.mapDerivedCategoryNatIso e).hom ≫
          (Functor.mapDerivedCategoryNatIso a1).hom ≫
          (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F a13)).hom) ≫
        (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).inv ≫
        Functor.whiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso G H).inv := by
            simpa only [Category.assoc] using ht
    _ = _ := by
      simp only [Category.assoc]
      rw [← Category.assoc (Functor.mapDerivedCategoryNatIso
        (Functor.isoWhiskerLeft F a13)).hom, hL]
      simp only [Category.assoc]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem derived_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) (A : Type (u + 1)) [CommRing A] :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (towerPullback A) e))).hom =
      (eqToIso (congrArg (G A) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem gComp_coherence {X Y Z W : Scheme.{u}}
    (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X) (A : Type (u + 1)) [CommRing A]
    (M : Derived A X) :
    (gComp A j (h ≫ k)).hom.app M ≫
        (G A j).map ((gComp A h k).hom.app M) =
      (eqToIso (congrArg (G A) (Category.assoc j h k).symm)).hom.app M ≫
        (gComp A (j ≫ h) k).hom.app M ≫
        (gComp A j h).hom.app ((G A k).obj M) := by
  let F₁ := towerPullback A k
  let F₂ := towerPullback A h
  let F₃ := towerPullback A j
  let F₀₂ := towerPullback A (h ≫ k)
  let F₁₃ := towerPullback A (j ≫ h)
  let a₀₂ := towerGComp A h k
  let a₁₃ := towerGComp A j h
  let a₀ := towerGComp A j (h ≫ k)
  let a₁ := towerGComp A (j ≫ h) k
  let e := eqToIso (congrArg (towerPullback A) (Category.assoc j h k).symm)
  have ho : a₀ ≪≫ Functor.isoWhiskerRight a₀₂ F₃ =
      e ≪≫ a₁ ≪≫ Functor.isoWhiskerLeft F₁ a₁₃ := tower_coherence j h k A
  have hh := descend_coherence F₁ F₂ F₃ F₀₂ F₁₃
    (towerPullback A (j ≫ h ≫ k)) (towerPullback A ((j ≫ h) ≫ k))
    a₀₂ a₁₃ a₀ a₁ e ho
  have hm := NatTrans.congr_app hh M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hm
  have he := congrArg (fun t ↦ t.app M) (derived_transport (Category.assoc j h k).symm A)
  change (Functor.mapDerivedCategoryNatIso e).hom.app M = _ at he
  rw [he] at hm
  simpa only [gComp, G, F₁, F₂, F₃, F₀₂, F₁₃, a₀₂, a₁₃, a₀, a₁, e,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] using hm

private lemma conjugate_triangle_assoc
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₃}
    {FG : C₀ ⥤ C₂} {GH : C₁ ⥤ C₃} {FGH : C₀ ⥤ C₃}
    {RF : C₁ ⥤ C₀} {RG : C₂ ⥤ C₁} {RH : C₃ ⥤ C₂}
    {RFG : C₂ ⥤ C₀} {RGH : C₃ ⥤ C₁} {RFGH : C₃ ⥤ C₀}
    (af : F ⊣ RF) (ag : G ⊣ RG) (ah : H ⊣ RH)
    (afg : FG ⊣ RFG) (agh : GH ⊣ RGH) (afgh : FGH ⊣ RFGH)
    (eFG : FG ≅ F ⋙ G) (eGH : GH ≅ G ⋙ H)
    (eF_GH : FGH ≅ F ⋙ GH) (eFG_H : FGH ≅ FG ⋙ H)
    (h : eF_GH.hom ≫ Functor.whiskerLeft F eGH.hom =
      eFG_H.hom ≫ Functor.whiskerRight eFG.hom H) :
    Functor.whiskerLeft RH (conjugateEquiv (af.comp ag) afg eFG.hom) ≫
        conjugateEquiv (afg.comp ah) afgh eFG_H.hom =
      Functor.whiskerRight (conjugateEquiv (ag.comp ah) agh eGH.hom) RF ≫
        conjugateEquiv (af.comp agh) afgh eF_GH.hom := by
  have hm : (Functor.associator RH RG RF).hom ≫
      (Functor.whiskerLeft RH (conjugateEquiv (af.comp ag) afg eFG.hom) ≫
        conjugateEquiv (afg.comp ah) afgh eFG_H.hom) =
      Functor.whiskerRight (conjugateEquiv (ag.comp ah) agh eGH.hom) RF ≫
        conjugateEquiv (af.comp agh) afgh eF_GH.hom := by
    rw [← conjugateEquiv_associator_hom af ag ah,
      ← conjugateEquiv_whiskerRight (af.comp ag) afg ah,
      ← conjugateEquiv_whiskerLeft (ag.comp ah) agh af,
      conjugateEquiv_comp, conjugateEquiv_comp, conjugateEquiv_comp]
    congr 1
    apply NatTrans.ext
    funext K
    simpa only [NatTrans.comp_app, Functor.associator_hom_app, Category.comp_id] using
      (NatTrans.congr_app h K).symm
  apply NatTrans.ext
  funext K
  simpa only [NatTrans.comp_app, Functor.associator_hom_app, Category.id_comp] using
    NatTrans.congr_app hm K

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def gCompEq {X Y Z : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A] (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : f ≫ g = h) : G A h ≅ G A g ⋙ G A f :=
  eqToIso (congrArg (G A) w.symm) ≪≫ gComp A f g

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem gCompEq_coherence {W X Y Z : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A] (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (abc : W ⟶ Z)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) :
    gCompEq A a bc abc hr ≪≫ Functor.isoWhiskerRight (gCompEq A b c bc hbc) (G A a) =
      gCompEq A ab c abc hl ≪≫ Functor.isoWhiskerLeft (G A c) (gCompEq A a b ab hab) := by
  subst ab bc
  cases hr
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [gCompEq, eqToIso_refl, Iso.refl_trans, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] using gComp_coherence a b c A M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem rCompEq_conjugate {X Y Z : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A] (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : f ≫ g = h) :
    rCompEq A f g h w =
      conjugateIsoEquiv ((adj A g).comp (adj A f)) (adj A h) (gCompEq A f g h w) := by
  exact rCompEq_spec A f g h w

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem rCompEq_coherence (A : Type (u + 1)) [CommRing A]
    {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (abc : W ⟶ Z)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) (M : Derived A W) :
    (R A c).map ((rCompEq A a b ab hab).hom.app M) ≫
        (rCompEq A ab c abc hl).hom.app M =
      (rCompEq A b c bc hbc).hom.app ((R A a).obj M) ≫
        (rCompEq A a bc abc hr).hom.app M := by
  have hg := congrArg Iso.hom (gCompEq_coherence A a b c ab bc abc hab hbc hl hr)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom] at hg
  have hh := conjugate_triangle_assoc (adj A c) (adj A b) (adj A a)
    (adj A bc) (adj A ab) (adj A abc)
    (gCompEq A b c bc hbc) (gCompEq A a b ab hab)
    (gCompEq A ab c abc hl) (gCompEq A a bc abc hr) hg.symm
  have hm := NatTrans.congr_app hh M
  simpa only [rCompEq_conjugate, conjugateIsoEquiv_apply_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] using hm.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem site_congr_transport
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y : C} {f g : X ⟶ Y} (e : f = g) :
    MorphismProperty.Over.pullbackCongr (P := P) (Q := Q) e =
      eqToIso (congrArg (fun t : X ⟶ Y ↦ MorphismProperty.Over.pullback P Q t) e) := by
  cases e
  exact MorphismProperty.Over.pullbackCongr_refl f rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem site_left_unit
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y : C} (f : X ⟶ Y) (U : P.Over Q Y) :
    eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U)
        (Category.id_comp f).symm) ≫
      (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) (𝟙 X) f).hom.app U =
      (MorphismProperty.Over.pullbackId P Q X).inv.app
        ((MorphismProperty.Over.pullback P Q f).obj U) := by
  have h := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_id_left (P := P) (Q := Q) f (𝟙 X ≫ f) rfl)) U
  rw [site_congr_transport] at h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app,
    eqToIso.hom, eqToHom_app] at h
  rw [h]
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem directId_hom_apply
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (N : Modules A X) (U : X.ProEt)
    (m : ((moduleDirectImage A (𝟙 X)).obj N).val.obj (Opposite.op U)) :
    ((moduleRId A X).hom.app N).val.app (Opposite.op U) m =
      N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U).op m := by
  exact (Classical.choose_spec (moduleRId_existsUnique A X)).1 N U m

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem restriction_eq
    {C : Type*} [Category C] {S : Cᵒᵖ ⥤ RingCat} (N : PresheafOfModules S)
    {U V : C} (a b : U ⟶ V) (h : a = b) (m : N.obj (Opposite.op V)) :
    N.map a.op m = N.map b.op m := by
  cases h
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem directImage_left_unit
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1)) [CommRing A] :
    moduleRComp A (𝟙 X) f ≪≫
        eqToIso (congrArg (moduleDirectImage A) (Category.id_comp f)) =
      Functor.isoWhiskerRight (moduleRId A X) (moduleDirectImage A f) ≪≫
        Functor.leftUnitor (moduleDirectImage A f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  ext m
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [directImage_map_apply f A ((moduleRId A X).hom.app N) U]
  erw [directId_hom_apply X A N ((Scheme.proEtaleBaseChange f).obj U)]
  erw [directImage_transport (Category.id_comp f) A N U]
  erw [directComp_hom_apply (𝟙 X) f A N U]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  exact restriction_eq N.val _ _ (site_left_unit (P := @WeaklyEtale) (Q := ⊤) f U) m

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def moduleGId (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    modulePullback A (𝟙 X) ≅ 𝟭 (Modules A X) :=
  Adjunction.leftAdjointIdIso (moduleAdj (𝟙 X) A) (moduleRId A X)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] (M : Modules A Y) :
    (eqToIso (congrArg (modulePullback A) (Category.id_comp f).symm)).hom.app M ≫
        (moduleGComp A (𝟙 X) f).hom.app M ≫
        (moduleGId A X).hom.app ((modulePullback A f).obj M) = 𝟙 _ := by
  have h := Adjunction.leftAdjointCompIso_comp_id (moduleAdj f A) (moduleAdj (𝟙 X) A)
    (moduleRComp A (𝟙 X) f ≪≫
      eqToIso (congrArg (moduleDirectImage A) (Category.id_comp f)))
    (moduleRId A X) (directImage_left_unit f A)
  rw [mate_transport (modulePullback A) (moduleDirectImage A)
    (fun t ↦ moduleAdj t A) (moduleAdj f A) (moduleAdj (𝟙 X) A)
      (Category.id_comp f) (moduleRComp A (𝟙 X) f)] at h
  have hi := NatTrans.congr_app (congrArg Iso.inv h) M
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app] at hi
  change (eqToIso (congrArg (modulePullback A)
    (Category.id_comp f).symm)).hom.app M ≫ (moduleGComp A (𝟙 X) f).hom.app M =
    𝟙 _ ≫ (moduleGId A X).inv.app ((modulePullback A f).obj M) at hi
  rw [← Category.assoc, hi]
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def towerGId (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    towerPullback A (𝟙 X) ≅ 𝟭 (Towers A X) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (moduleGId A X) ≪≫
    Functor.whiskeringRightObjIdIso

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tower_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    eqToIso (congrArg (towerPullback A) (Category.id_comp f).symm) ≪≫
        towerGComp A (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft (towerPullback A f) (towerGId A X) ≪≫
        Functor.rightUnitor (towerPullback A f) = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    towerGComp_app, Iso.refl_hom, NatTrans.id_app]
  change ((eqToIso (congrArg (modulePullback A)
    (Category.id_comp f).symm)).hom.app (M.obj n) ≫
      (moduleGComp A (𝟙 X) f).hom.app (M.obj n)) ≫
      ((moduleGId A X).hom.app ((modulePullback A f).obj (M.obj n)) ≫ 𝟙 _) = 𝟙 _
  simpa only [Category.comp_id, Category.assoc] using ordinary_left_unit f A (M.obj n)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem descend_left_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F H : C ⥤ D) (I : D ⥤ D)
    [F.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (q : F ≅ H) (k : H ≅ F ⋙ I) (e : I ≅ 𝟭 D)
    (ho : q ≪≫ k ≪≫ Functor.isoWhiskerLeft F e ≪≫
      Functor.rightUnitor F = Iso.refl F) :
    (Functor.mapDerivedCategoryNatIso q).hom ≫
        (Functor.mapDerivedCategoryNatIso k).hom ≫
        (Functor.mapDerivedCategoryCompIso F I).inv ≫
        Functor.whiskerLeft F.mapDerivedCategory
          ((Functor.mapDerivedCategoryNatIso e).hom ≫
            (Functor.mapDerivedCategoryIdIso D).hom) = 𝟙 _ := by
  have hd := congrArg (fun t ↦ (Functor.mapDerivedCategoryNatIso t).hom) ho
  simp only [Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_refl] at hd
  have hr : (Functor.mapDerivedCategoryNatIso (Functor.rightUnitor F)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  rw [hr, Category.comp_id] at hd
  rw [Functor.whiskerLeft_comp]
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F I).inv,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_comp_id]
  erw [Category.comp_id]
  simpa only [Category.assoc] using hd

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem gCompEq_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    gCompEq A (𝟙 X) f f (Category.id_comp f) ≪≫
        Functor.isoWhiskerLeft (G A f) (gId A X) ≪≫
        Functor.rightUnitor (G A f) = Iso.refl _ := by
  have hh := descend_left_unit (towerPullback A f) (towerPullback A (𝟙 X ≫ f))
    (towerPullback A (𝟙 X))
    (eqToIso (congrArg (towerPullback A) (Category.id_comp f).symm))
    (towerGComp A (𝟙 X) f) (towerGId A X) (tower_left_unit f A)
  rw [derived_transport (Category.id_comp f).symm A] at hh
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hm := NatTrans.congr_app hh M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Iso.refl_hom, NatTrans.id_app]
  erw [Category.comp_id]
  simpa only [gCompEq, gComp, gId, towerGId, moduleGId, moduleAdj, G,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Functor.map_comp, Category.assoc, Category.comp_id] using hm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem conjugate_unit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R : D ⥤ C} {I RI : D ⥤ D}
    (a : F ⊣ R) (b : I ⊣ RI) (e : I ≅ 𝟭 D) (k : F ≅ F ⋙ I)
    (h : k ≪≫ Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F = Iso.refl F) :
    conjugateIsoEquiv (a.comp b) a k =
      Functor.isoWhiskerRight (conjugateIsoEquiv b Adjunction.id e.symm) R ≪≫
        Functor.leftUnitor R := by
  have hk : k = (Functor.rightUnitor F).symm ≪≫
      Functor.isoWhiskerLeft F e.symm := by
    apply Iso.ext
    have hh := congrArg Iso.hom h
    change k.hom ≫ (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F).hom = 𝟙 _ at hh
    have hi := (Iso.comp_hom_eq_id
      (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F)).1 hh
    simpa only [Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerLeft_symm,
      Iso.symm_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom] using hi
  rw [hk, conjugateIsoEquiv_trans (a.comp b) (a.comp Adjunction.id) a,
    conjugateIsoEquiv_isoWhiskerLeft b Adjunction.id a,
    conjugateIsoEquiv_iso_symm a (a.comp Adjunction.id),
    conjugateIsoEquiv_rightUnitor, Iso.symm_symm_eq]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem rCompEq_left_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived A X) :
    (rCompEq A (𝟙 X) f f (Category.id_comp f)).hom.app M =
      (R A f).map ((rId A X).hom.app M) := by
  have h := conjugate_unit (adj A f) (adj A (𝟙 X)) (gId A X)
    (gCompEq A (𝟙 X) f f (Category.id_comp f)) (gCompEq_left_unit f A)
  rw [← rCompEq_conjugate] at h
  have hm := NatTrans.congr_app (congrArg Iso.hom h) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    conjugateIsoEquiv_iso_symm] at hm
  erw [Category.comp_id] at hm
  exact hm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem site_right_unit
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y : C} (f : X ⟶ Y) (U : P.Over Q Y) :
    eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U)
        (Category.comp_id f).symm) ≫
      (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f (𝟙 Y)).hom.app U =
      (MorphismProperty.Over.pullback P Q f).map
        ((MorphismProperty.Over.pullbackId P Q Y).inv.app U) := by
  have h := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_id_right (P := P) (Q := Q) f (f ≫ 𝟙 Y) rfl)) U
  rw [site_congr_transport] at h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app,
    eqToIso.hom, eqToHom_app] at h
  rw [h]
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem directImage_right_unit
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1)) [CommRing A] :
    moduleRComp A f (𝟙 Y) ≪≫
        eqToIso (congrArg (moduleDirectImage A) (Category.comp_id f)) =
      Functor.isoWhiskerLeft (moduleDirectImage A f) (moduleRId A Y) ≪≫
        Functor.rightUnitor (moduleDirectImage A f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  ext m
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [directId_hom_apply Y A ((moduleDirectImage A f).obj N) U]
  erw [directImage_obj_map_apply f A N
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).inv.app U)]
  erw [directImage_transport (Category.comp_id f) A N U]
  erw [directComp_hom_apply f (𝟙 Y) A N U]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  exact restriction_eq N.val _ _ (site_right_unit (P := @WeaklyEtale) (Q := ⊤) f U) m

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] (M : Modules A Y) :
    (eqToIso (congrArg (modulePullback A) (Category.comp_id f).symm)).hom.app M ≫
        (moduleGComp A f (𝟙 Y)).hom.app M ≫
        (modulePullback A f).map ((moduleGId A Y).hom.app M) = 𝟙 _ := by
  have h := Adjunction.leftAdjointCompIso_id_comp (moduleAdj (𝟙 Y) A) (moduleAdj f A)
    (moduleRComp A f (𝟙 Y) ≪≫
      eqToIso (congrArg (moduleDirectImage A) (Category.comp_id f)))
    (moduleRId A Y) (directImage_right_unit f A)
  rw [mate_transport (modulePullback A) (moduleDirectImage A)
    (fun t ↦ moduleAdj t A) (moduleAdj (𝟙 Y) A) (moduleAdj f A)
      (Category.comp_id f) (moduleRComp A f (𝟙 Y))] at h
  have hi := NatTrans.congr_app (congrArg Iso.inv h) M
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app] at hi
  change (eqToIso (congrArg (modulePullback A)
    (Category.comp_id f).symm)).hom.app M ≫ (moduleGComp A f (𝟙 Y)).hom.app M =
    𝟙 _ ≫ (modulePullback A f).map ((moduleGId A Y).inv.app M) at hi
  rw [← Category.assoc, hi]
  simp [← Functor.map_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tower_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    eqToIso (congrArg (towerPullback A) (Category.comp_id f).symm) ≪≫
        towerGComp A f (𝟙 Y) ≪≫
        Functor.isoWhiskerRight (towerGId A Y) (towerPullback A f) ≪≫
        Functor.leftUnitor (towerPullback A f) = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    towerGComp_app, tower_map_app, Iso.refl_hom, NatTrans.id_app]
  change ((eqToIso (congrArg (modulePullback A)
    (Category.comp_id f).symm)).hom.app (M.obj n) ≫
      (moduleGComp A f (𝟙 Y)).hom.app (M.obj n)) ≫
      (modulePullback A f).map ((moduleGId A Y).hom.app (M.obj n) ≫ 𝟙 _) = 𝟙 _
  simpa only [Category.comp_id, Category.assoc] using ordinary_right_unit f A (M.obj n)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem descend_right_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F H : C ⥤ D) (I : C ⥤ C)
    [F.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (q : F ≅ H) (k : H ≅ I ⋙ F) (e : I ≅ 𝟭 C)
    (ho : q ≪≫ k ≪≫ Functor.isoWhiskerRight e F ≪≫
      Functor.leftUnitor F = Iso.refl F) :
    (Functor.mapDerivedCategoryNatIso q).hom ≫
        (Functor.mapDerivedCategoryNatIso k).hom ≫
        (Functor.mapDerivedCategoryCompIso I F).inv ≫
        Functor.whiskerRight ((Functor.mapDerivedCategoryNatIso e).hom ≫
          (Functor.mapDerivedCategoryIdIso C).hom) F.mapDerivedCategory = 𝟙 _ := by
  have hd := congrArg (fun t ↦ (Functor.mapDerivedCategoryNatIso t).hom) ho
  simp only [Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_refl] at hd
  have hr : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor F)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  rw [hr, Category.comp_id] at hd
  rw [Functor.whiskerRight_comp]
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso I F).inv,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerRight e F]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_id_comp]
  erw [Category.comp_id]
  simpa only [Category.assoc] using hd

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem gCompEq_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    gCompEq A f (𝟙 Y) f (Category.comp_id f) ≪≫
        Functor.isoWhiskerRight (gId A Y) (G A f) ≪≫
        Functor.leftUnitor (G A f) = Iso.refl _ := by
  have hh := descend_right_unit (towerPullback A f) (towerPullback A (f ≫ 𝟙 Y))
    (towerPullback A (𝟙 Y))
    (eqToIso (congrArg (towerPullback A) (Category.comp_id f).symm))
    (towerGComp A f (𝟙 Y)) (towerGId A Y) (tower_right_unit f A)
  rw [derived_transport (Category.comp_id f).symm A] at hh
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hm := NatTrans.congr_app hh M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.refl_hom, NatTrans.id_app]
  erw [Category.comp_id]
  simpa only [gCompEq, gComp, gId, towerGId, moduleGId, moduleAdj, G,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.map_comp, Category.assoc, NatTrans.id_app,
    Functor.comp_obj, Functor.id_obj] using hm

attribute [local irreducible] G R rId rComp adj exchange towers_hasDerivedCategory

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Contravariant functor families on schemes.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: lem-cbc-strict-tower-direct-image-coherence). -/
abbrev InverseImageFamily (C : Scheme.{u} → Type*)
    [∀ X, Category.{u + 2} (C X)] :=
  ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (C Y ⥤ C X)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Covariant functor families on schemes.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: lem-cbc-strict-tower-direct-image-coherence). -/
abbrev DirectImageFamily (C : Scheme.{u} → Type*)
    [∀ X, Category.{u + 2} (C X)] :=
  ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (C X ⥤ C Y)

attribute [-instance] CategoryTheory.catToReflQuiver in
private abbrev AdjunctionFamily (C : Scheme.{u} → Type*)
    [∀ X, Category.{u + 2} (C X)]
    (L : InverseImageFamily C) (R₀ : DirectImageFamily C) :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), L f ⊣ R₀ f

attribute [-instance] CategoryTheory.catToReflQuiver in
private abbrev CompositionFamily (C : Scheme.{u} → Type*)
    [∀ X, Category.{u + 2} (C X)] (L : InverseImageFamily C) :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z), f ≫ g = h → (L h ≅ L g ⋙ L f)

attribute [-instance] CategoryTheory.catToReflQuiver in
private abbrev UnitFamily (C : Scheme.{u} → Type*)
    [∀ X, Category.{u + 2} (C X)] (L : InverseImageFamily C) :=
  ∀ X, L (𝟙 X) ≅ 𝟭 (C X)

attribute [-instance] CategoryTheory.catToReflQuiver in
private structure PullbackCoherentSystem (C : Scheme.{u} → Type*)
    [∀ X, Category.{u + 2} (C X)]
    (L : InverseImageFamily C) (R₀ : DirectImageFamily C)
    (_adj₀ : AdjunctionFamily C L R₀) (κ : CompositionFamily C L)
    (ε : UnitFamily C L) : Prop where
  assoc : ∀ {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (abc : W ⟶ Z)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc),
    κ a bc abc hr ≪≫ Functor.isoWhiskerRight (κ b c bc hbc) (L a) =
      κ ab c abc hl ≪≫ Functor.isoWhiskerLeft (L c) (κ a b ab hab)
  left_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    κ (𝟙 X) f f (Category.id_comp f) ≪≫
      Functor.isoWhiskerLeft (L f) (ε X) ≪≫ Functor.rightUnitor (L f) = Iso.refl _
  right_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    κ f (𝟙 Y) f (Category.comp_id f) ≪≫
      Functor.isoWhiskerRight (ε Y) (L f) ≪≫ Functor.leftUnitor (L f) = Iso.refl _

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def systemSquare {C : Scheme.{u} → Type*} [∀ X, Category.{u + 2} (C X)]
    {L : InverseImageFamily C} (κ : CompositionFamily C L)
    {W X Y Z : Scheme.{u}} (a : W ⟶ X) (f' : W ⟶ Y) (f : X ⟶ Z) (b : Y ⟶ Z)
    (w : a ≫ f = f' ≫ b) : L b ⋙ L f' ≅ L f ⋙ L a :=
  (κ f' b (a ≫ f) w.symm).symm ≪≫ κ a f (a ≫ f) rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem rearrange_square {D : Type*} [Category D] {P Q R T : D}
    (a : P ⟶ Q) (b : P ⟶ R) (x : Q ⟶ T) (y : R ⟶ T)
    [IsIso a] [IsIso y] (h : a ≫ x = b ≫ y) : x ≫ inv y = inv a ≫ b := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, h, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

section SystemPasting

attribute [-instance] CategoryTheory.catToReflQuiver in
@[reassoc]
private theorem system_map_hom_inv {C : Scheme.{u} → Type*}
    [∀ X, Category.{u + 2} (C X)] {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {adj₀ : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (S : PullbackCoherentSystem C L R₀ adj₀ κ ε)
    {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (abc : W ⟶ Z)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) (M : C Z) :
    (L a).map ((κ b c bc hbc).hom.app M) ≫
        (κ a b ab hab).inv.app ((L c).obj M) =
      (κ a bc abc hr).inv.app M ≫ (κ ab c abc hl).hom.app M := by
  have key := NatTrans.congr_app (congrArg Iso.hom
    (S.assoc a b c ab bc abc hab hbc hl hr)) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
  simpa only [NatIso.inv_hom_app] using rearrange_square _ _ _ _ key

attribute [-instance] CategoryTheory.catToReflQuiver in
@[reassoc]
private theorem system_comp_hom_map_inv {C : Scheme.{u} → Type*}
    [∀ X, Category.{u + 2} (C X)] {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {adj₀ : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (S : PullbackCoherentSystem C L R₀ adj₀ κ ε)
    {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (abc : W ⟶ Z)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) (M : C Z) :
    (κ a b ab hab).hom.app ((L c).obj M) ≫
        (L a).map ((κ b c bc hbc).inv.app M) =
      (κ ab c abc hl).inv.app M ≫ (κ a bc abc hr).hom.app M := by
  have key := NatTrans.congr_app (congrArg Iso.hom
    (S.assoc a b c ab bc abc hab hbc hl hr)) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
  have hh := rearrange_square _ _ _ _ key.symm
  rwa [NatIso.inv_hom_app, ← Functor.map_inv, NatIso.inv_hom_app] at hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_square_vertical {C : Scheme.{u} → Type*}
    [∀ X, Category.{u + 2} (C X)] {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {adj₀ : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (S : PullbackCoherentSystem C L R₀ adj₀ κ ε)
    {W X Y W' X' Y' : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : W ⟶ Y)
    (f' : W' ⟶ X') (g' : X' ⟶ Y') (h' : W' ⟶ Y')
    (a : W' ⟶ W) (b : X' ⟶ X) (c : Y' ⟶ Y)
    (w : f ≫ g = h) (w' : f' ≫ g' = h')
    (wf : a ≫ f = f' ≫ b) (wg : b ≫ g = g' ≫ c)
    (wh : a ≫ h = h' ≫ c) :
    (TwoSquare.vComp
      (TwoSquare.mk (L c) (L g) (L g') (L b)
        (systemSquare κ b g' g c wg).hom)
      (TwoSquare.mk (L b) (L f) (L f') (L a)
        (systemSquare κ a f' f b wf).hom)).whiskerLeft
        (κ f g h w).inv =
      (TwoSquare.mk (L c) (L h) (L h') (L a)
        (systemSquare κ a h' h c wh).hom).whiskerRight
        (κ f' g' h' w').inv := by
  ext M
  simp only [systemSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vComp_app,
    Functor.map_comp, Category.assoc]
  rw [system_map_hom_inv_assoc S f' b g (a ≫ f) (b ≫ g) (a ≫ h)
    wf.symm rfl (by rw [Category.assoc, w]) (by rw [← Category.assoc, ← wf, Category.assoc, w])]
  rw [system_comp_hom_map_inv S a f g (a ≫ f) h (a ≫ h)
    rfl w (by rw [Category.assoc, w]) rfl]
  rw [Iso.hom_inv_id_app_assoc]
  have key := NatTrans.congr_app (congrArg Iso.inv
    (S.assoc f' g' c h' (b ≫ g) (a ≫ h) w' wg.symm wh.symm
      (by rw [← Category.assoc, ← wf, Category.assoc, w]))) M
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
  rw [← Category.assoc, key]
  simp only [Category.assoc]

end SystemPasting

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_k_transport {C : Scheme.{u} → Type*} [∀ X, Category.{u + 2} (C X)]
    {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {adj₀ : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (_S : PullbackCoherentSystem C L R₀ adj₀ κ ε)
    {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h t : X ⟶ Z) (w : f ≫ g = h) (v : h = t) :
    κ f g t (w.trans v) = eqToIso (congrArg L v.symm) ≪≫ κ f g h w := by
  subst t
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_square_normalize {C : Scheme.{u} → Type*} [∀ X, Category.{u + 2} (C X)]
    {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {adj₀ : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (S : PullbackCoherentSystem C L R₀ adj₀ κ ε)
    {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (f' : W ⟶ Y) (f : X ⟶ Z) (b : Y ⟶ Z)
    (w : a ≫ f = f' ≫ b) (t : W ⟶ Z)
    (wa : a ≫ f = t) (wb : f' ≫ b = t) :
    systemSquare κ a f' f b w = (κ f' b t wb).symm ≪≫ κ a f t wa := by
  rw [system_k_transport S f' b (a ≫ f) t w.symm wa,
    system_k_transport S a f (a ≫ f) t rfl wa]
  simp [systemSquare]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_square_identity {C : Scheme.{u} → Type*} [∀ X, Category.{u + 2} (C X)]
    {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {adj₀ : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (S : PullbackCoherentSystem C L R₀ adj₀ κ ε)
    {X X' : Scheme.{u}} (a : X' ⟶ X)
    (w : a ≫ (𝟙 X) = (𝟙 X') ≫ a) :
    (TwoSquare.mk _ _ _ _ (systemSquare κ a (𝟙 X') (𝟙 X) a w).hom).whiskerLeft
        (ε X).hom =
      (TwoSquare.vId (L a)).whiskerRight (ε X').hom := by
  ext M
  rw [system_square_normalize S a (𝟙 X') (𝟙 X) a w a
    (Category.comp_id a) (Category.id_comp a)]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vId_app]
  have hl := NatTrans.congr_app (congrArg Iso.hom (S.left_unit a)) M
  have hr := NatTrans.congr_app (congrArg Iso.hom (S.right_unit a)) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Iso.refl_hom, NatTrans.id_app] at hl hr
  erw [Category.comp_id] at hl hr
  erw [Category.comp_id]
  rw [Category.assoc, hr, Category.comp_id]
  apply (cancel_epi ((κ (𝟙 X') a a (Category.id_comp a)).hom.app M)).1
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using hl.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def systemExchange {C : Scheme.{u} → Type*}
    [∀ X, Category.{u + 2} (C X)] {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    (adj₀ : AdjunctionFamily C L R₀) (κ : CompositionFamily C L)
    {W X Y Z : Scheme.{u}} (a : W ⟶ X) (f' : W ⟶ Y) (f : X ⟶ Z) (b : Y ⟶ Z)
    (w : a ≫ f = f' ≫ b) : R₀ f ⋙ L b ⟶ L a ⋙ R₀ f' :=
  mateEquiv (adj₀ f) (adj₀ f')
    (TwoSquare.mk _ _ _ _ (systemSquare κ a f' f b w).hom)

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def systemRId {C : Scheme.{u} → Type*}
    [∀ X, Category.{u + 2} (C X)] {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    (adj₀ : AdjunctionFamily C L R₀) (ε : UnitFamily C L) (X : Scheme.{u}) :
    R₀ (𝟙 X) ≅ 𝟭 (C X) :=
  (conjugateIsoEquiv Adjunction.id (adj₀ (𝟙 X)) (ε X)).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def systemRComp {C : Scheme.{u} → Type*}
    [∀ X, Category.{u + 2} (C X)] {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    (adj₀ : AdjunctionFamily C L R₀) (κ : CompositionFamily C L)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    R₀ f ⋙ R₀ g ≅ R₀ h :=
  conjugateIsoEquiv ((adj₀ g).comp (adj₀ f)) (adj₀ h) (κ f g h w)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_exchange_identity {C : Scheme.{u} → Type*}
    [∀ X, Category.{u + 2} (C X)] {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {adj₀ : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (S : PullbackCoherentSystem C L R₀ adj₀ κ ε)
    {X X' : Scheme.{u}} (a : X' ⟶ X)
    (w : a ≫ (𝟙 X) = (𝟙 X') ≫ a) (M : C X) :
    (systemExchange adj₀ κ a (𝟙 X') (𝟙 X) a w).app M ≫
        (systemRId adj₀ ε X').hom.app ((L a).obj M) =
      (L a).map ((systemRId adj₀ ε X).hom.app M) := by
  have h := mateEquiv_whiskerTop_conjugateEquiv
    Adjunction.id (adj₀ (𝟙 X)) Adjunction.id (adj₀ (𝟙 X'))
    (ε X).hom (ε X').hom (TwoSquare.vId (L a))
    (TwoSquare.mk _ _ _ _ (systemSquare κ a (𝟙 X') (𝟙 X) a w).hom)
    (system_square_identity S a w)
  dsimp only [TwoSquare.vId] at h
  rw [mateEquiv_id_id_unitors] at h
  have hm := NatTrans.congr_app h M
  change (L a).map ((systemRId adj₀ ε X).inv.app M) ≫
    (systemExchange adj₀ κ a (𝟙 X') (𝟙 X) a w).app M =
    (𝟙 _ ≫ 𝟙 _) ≫ (systemRId adj₀ ε X').inv.app ((L a).obj M) at hm
  simp only [Category.id_comp] at hm
  apply (cancel_epi ((L a).map ((systemRId adj₀ ε X).inv.app M))).1
  rw [← Category.assoc, hm]
  simp [← Functor.map_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_exchange_vertical {C : Scheme.{u} → Type*}
    [∀ X, Category.{u + 2} (C X)] {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {adj₀ : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (S : PullbackCoherentSystem C L R₀ adj₀ κ ε)
    {W X Y W' X' Y' : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : W ⟶ Y)
    (f' : W' ⟶ X') (g' : X' ⟶ Y') (h' : W' ⟶ Y')
    (a : W' ⟶ W) (b : X' ⟶ X) (c : Y' ⟶ Y)
    (w : f ≫ g = h) (w' : f' ≫ g' = h')
    (wf : a ≫ f = f' ≫ b) (wg : b ≫ g = g' ≫ c)
    (wh : a ≫ h = h' ≫ c) (M : C W) :
    (L c).map ((systemRComp adj₀ κ f g h w).hom.app M) ≫
        (systemExchange adj₀ κ a h' h c wh).app M =
      (systemExchange adj₀ κ b g' g c wg).app ((R₀ f).obj M) ≫
        (R₀ g').map ((systemExchange adj₀ κ a f' f b wf).app M) ≫
        (systemRComp adj₀ κ f' g' h' w').hom.app ((L a).obj M) := by
  have hh := mateEquiv_whiskerTop_conjugateEquiv
    (adj₀ h) ((adj₀ g).comp (adj₀ f))
    (adj₀ h') ((adj₀ g').comp (adj₀ f'))
    (κ f g h w).inv (κ f' g' h' w').inv
    (TwoSquare.mk _ _ _ _ (systemSquare κ a h' h c wh).hom)
    (TwoSquare.vComp
      (TwoSquare.mk _ _ _ _ (systemSquare κ b g' g c wg).hom)
      (TwoSquare.mk _ _ _ _ (systemSquare κ a f' f b wf).hom))
    (system_square_vertical S f g h f' g' h' a b c w w' wf wg wh)
  rw [mateEquiv_hcomp] at hh
  have hm := NatTrans.congr_app hh M
  simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
    TwoSquare.hComp_app] at hm
  change (L c).map ((systemRComp adj₀ κ f g h w).inv.app M) ≫
    ((systemExchange adj₀ κ b g' g c wg).app ((R₀ f).obj M) ≫
      (R₀ g').map ((systemExchange adj₀ κ a f' f b wf).app M)) =
    (systemExchange adj₀ κ a h' h c wh).app M ≫
      (systemRComp adj₀ κ f' g' h' w').inv.app ((L a).obj M) at hm
  have hp := rearrange_square _ _ _ _ hm
  simpa only [← Functor.map_inv, NatIso.inv_inv_app, Category.assoc] using hp.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Composition isomorphisms with a supplied equation for the composite.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: lem-cbc-strict-tower-direct-image-coherence). -/
abbrev RightCompositionFamily (C : Scheme.{u} → Type*)
    [∀ X, Category.{u + 2} (C X)] (R₀ : DirectImageFamily C) :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z),
    f ≫ g = h → (R₀ f ⋙ R₀ g ≅ R₀ h)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Natural transformations for arbitrary commutative squares.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: lem-cbc-strict-tower-direct-image-coherence). -/
abbrev ExchangeFamily (C : Scheme.{u} → Type*)
    [∀ X, Category.{u + 2} (C X)]
    (L : InverseImageFamily C) (R₀ : DirectImageFamily C) :=
  ∀ {W X Y Z : Scheme.{u}} (a : W ⟶ X) (f' : W ⟶ Y) (f : X ⟶ Z) (b : Y ⟶ Z),
    a ≫ f = f' ≫ b → (R₀ f ⋙ L b ⟶ L a ⋙ R₀ f')

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Square mates respect vertical pasting and direct-image composition.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: lem-cbc-strict-tower-direct-image-coherence). -/
def matePastingLaw {C : Scheme.{u} → Type*} [∀ X, Category.{u + 2} (C X)]
    (L : InverseImageFamily C) (R₀ : DirectImageFamily C)
    (K : RightCompositionFamily C R₀) (E : ExchangeFamily C L R₀) : Prop :=
  ∀ (W X Y W' X' Y' : Scheme.{u})
    (f : W ⟶ X) (g : X ⟶ Y) (h : W ⟶ Y)
    (f' : W' ⟶ X') (g' : X' ⟶ Y') (h' : W' ⟶ Y')
    (a : W' ⟶ W) (b : X' ⟶ X) (c : Y' ⟶ Y)
    (w : f ≫ g = h) (w' : f' ≫ g' = h')
    (wf : a ≫ f = f' ≫ b) (wg : b ≫ g = g' ≫ c)
    (wh : a ≫ h = h' ≫ c) (M : C W),
    (L c).map ((K f g h w).hom.app M) ≫ (E a h' h c wh).app M =
      (E b g' g c wg).app ((R₀ f).obj M) ≫
        (R₀ g').map ((E a f' f b wf).app M) ≫
          (K f' g' h' w').hom.app ((L a).obj M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_matePastingLaw {C : Scheme.{u} → Type*}
    [∀ X, Category.{u + 2} (C X)] {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {adj₀ : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (S : PullbackCoherentSystem C L R₀ adj₀ κ ε) :
    matePastingLaw L R₀
      (fun {_ _ _} f g h w ↦ systemRComp adj₀ κ f g h w)
      (fun {_ _ _ _} a f' f b w ↦ systemExchange adj₀ κ a f' f b w) := by
  intro W X Y W' X' Y' f g h f' g' h' a b c w w' wf wg wh M
  exact system_exchange_vertical S f g h f' g' h' a b c w w' wf wg wh M

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The identity-vertical square mate respects direct-image units.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: lem-cbc-strict-tower-direct-image-coherence). -/
def mateIdentityLaw {C : Scheme.{u} → Type*} [∀ X, Category.{u + 2} (C X)]
    (L : InverseImageFamily C) (R₀ : DirectImageFamily C)
    (I : ∀ X, R₀ (𝟙 X) ≅ 𝟭 (C X)) (E : ExchangeFamily C L R₀) : Prop :=
  ∀ (X X' : Scheme.{u}) (a : X' ⟶ X)
    (w : a ≫ (𝟙 X) = (𝟙 X') ≫ a) (M : C X),
    (E a (𝟙 X') (𝟙 X) a w).app M ≫ (I X').hom.app ((L a).obj M) =
      (L a).map ((I X).hom.app M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_mateIdentityLaw {C : Scheme.{u} → Type*}
    [∀ X, Category.{u + 2} (C X)] {L : InverseImageFamily C} {R₀ : DirectImageFamily C}
    {adj₀ : AdjunctionFamily C L R₀} {κ : CompositionFamily C L}
    {ε : UnitFamily C L} (S : PullbackCoherentSystem C L R₀ adj₀ κ ε) :
    mateIdentityLaw L R₀ (systemRId adj₀ ε)
      (fun {_ _ _ _} a f' f b w ↦ systemExchange adj₀ κ a f' f b w) := by
  intro X X' a w M
  exact system_exchange_identity S a w M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pullbackSystem (A : Type (u + 1)) [CommRing A] :
    PullbackCoherentSystem (Derived A) (G A) (R A) (adj A) (gCompEq A) (gId A) where
  assoc := gCompEq_coherence A
  left_unit f := gCompEq_left_unit f A
  right_unit f := gCompEq_right_unit f A

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem normalizeIsoSquare {D : Type*} [Category D]
    {X Y Z W : D} (e : X ≅ Y) (f : Z ≅ W) (h : X = Z) :
    e.symm ≪≫ eqToIso h ≪≫ f =
      (eqToIso h.symm ≪≫ e).symm ≪≫ (Iso.refl Z ≪≫ f) := by
  cases h
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem squareG_system {W X Y Z : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A]
    (a : W ⟶ X) (f' : W ⟶ Y) (f : X ⟶ Z) (b : Y ⟶ Z)
    (w : a ≫ f = f' ≫ b) :
    squareG A a f' f b w = systemSquare (gCompEq A) a f' f b w := by
  exact normalizeIsoSquare (gComp A f' b) (gComp A a f)
    (congrArg (G A) w.symm)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_exchange_eq {W X Y Z : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A]
    (a : W ⟶ X) (f' : W ⟶ Y) (f : X ⟶ Z) (b : Y ⟶ Z)
    (w : a ≫ f = f' ≫ b) :
    systemExchange (adj A) (gCompEq A) a f' f b w = exchange A a f' f b w := by
  unfold systemExchange
  rw [← squareG_system]
  unfold exchange
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_rId_eq (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    systemRId (adj A) (gId A) X = rId A X := by
  unfold rId
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_rComp_eq {X Y Z : Scheme.{u}}
    (A : Type (u + 1)) [CommRing A] (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) :
    systemRComp (adj A) (gCompEq A) f g h w = rCompEq A f g h w :=
  (rCompEq_conjugate A f g h w).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem concrete_mateIdentityLaw (A : Type (u + 1)) [CommRing A] :
    mateIdentityLaw (G A) (R A) (rId A) (@exchange.{u} A _) := by
  let I : ∀ X, R A (𝟙 X) ≅ 𝟭 (Derived A X) := systemRId (adj A) (gId A)
  let E : ExchangeFamily (Derived A) (G A) (R A) :=
    fun {_ _ _ _} a f' f b w ↦ systemExchange (adj A) (gCompEq A) a f' f b w
  have hI : I = rId A := by
    funext X
    exact system_rId_eq A X
  have hE : @E = @exchange.{u} A _ := by
    funext W X Y Z a f' f b w
    exact system_exchange_eq A a f' f b w
  exact (congrArg₂ (mateIdentityLaw (G A) (R A)) hI hE).mp
    (system_mateIdentityLaw (pullbackSystem A))

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem concrete_matePastingLaw (A : Type (u + 1)) [CommRing A] :
    matePastingLaw (G A) (R A) (@rCompEq.{u} A _) (@exchange.{u} A _) := by
  let K : RightCompositionFamily (Derived A) (R A) :=
    fun {_ _ _} f g h w ↦ systemRComp (adj A) (gCompEq A) f g h w
  let E : ExchangeFamily (Derived A) (G A) (R A) :=
    fun {_ _ _ _} a f' f b w ↦ systemExchange (adj A) (gCompEq A) a f' f b w
  have hK : @K = @rCompEq.{u} A _ := by
    funext X Y Z f g h w
    exact system_rComp_eq A f g h w
  have hE : @E = @exchange.{u} A _ := by
    funext W X Y Z a f' f b w
    exact system_exchange_eq A a f' f b w
  exact (congrArg₂ (matePastingLaw (G A) (R A)) hK hE).mp
    (system_matePastingLaw (pullbackSystem A))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The canonical square mates respect direct-image composition.
Source: Stacks, Tag 07A7
(blueprint: lem-cbc-strict-tower-direct-image-coherence).
Proof: the full compositor and exchange family equalities transport formal mate pasting. -/
theorem strictTowerMatePasting :
    matePastingLaw (G B) (R B) (@rCompEq.{u} B _) (@exchange.{u} B _) :=
  concrete_matePastingLaw B

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The four canonical direct-image and square-mate normalization equations.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: lem-cbc-strict-tower-direct-image-coherence). -/
def DirectImageCoherence : Prop :=
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived B X),
      (rCompEq B (𝟙 X) f f (Category.id_comp f)).hom.app M =
        (R B f).map ((rId B X).hom.app M)) ∧
    (∀ {W X Y Z : Scheme.{u}}
      (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
      (ab : W ⟶ Y) (bc : X ⟶ Z) (abc : W ⟶ Z)
      (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
      (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) (M : Derived B W),
      (R B c).map ((rCompEq B a b ab hab).hom.app M) ≫
          (rCompEq B ab c abc hl).hom.app M =
        (rCompEq B b c bc hbc).hom.app ((R B a).obj M) ≫
          (rCompEq B a bc abc hr).hom.app M) ∧
    mateIdentityLaw (G B) (R B) (rId B) (@exchange.{u} B _) ∧
    matePastingLaw (G B) (R B) (@rCompEq.{u} B _) (@exchange.{u} B _)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem packedDirectImageCoherence_proof : DirectImageCoherence B := by
  exact ⟨@rCompEq_left_unit.{u} B _, @rCompEq_coherence.{u} B _,
    @concrete_mateIdentityLaw.{u} B _, @concrete_matePastingLaw.{u} B _⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The canonical direct-image compositors are unital and associative, and the
canonical proper-square mates preserve identity maps and pasting.
Source: Stacks, Tags 0D6D and 07A7; the canonical composition and mate normalizations
(blueprint: lem-cbc-strict-tower-direct-image-coherence).

Proof: first check the module direct-image comparisons on sections. Their components
are restriction along the canonical pullback composition and identity isomorphisms.
Pullback pasting gives their triangle and pentagon equations. The uniqueness in
moduleRComp_existsUnique and moduleRId_existsUnique identifies these section maps
with the published choices. Conjugate through the module adjunctions to get the
same equations for module pullback. Termwise whiskering to towers and complexes
and exact localization preserve them, giving the equations for gComp and gId.
Conjugate again through the derived adjunctions: conjugation respects composition,
associators and unitors, giving the first two clauses of DirectImageCoherence for rComp and rId.
For the last two equations expand squareG. The pullback triangle equation identifies
the identity square with the two identity comparisons. The pentagon equation
identifies the square of a pasted rectangle with the two pasted square comparisons.
Take proper-adjunction mates. Mate pasting and the two conjugation equations for
composite adjunctions give exactly the displayed identity and pasting equations.
All these equalities hold before evaluation, on every derived strict tower. -/
theorem strictTowerDirectImageCoherence : DirectImageCoherence B := by
  exact packedDirectImageCoherence_proof B

end AlgebraicGeometry.ProEtale.StrictTower
