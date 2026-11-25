/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting

/-!
# Coherence of normalized semilinear compositors

Source: Stacks Project, Tags 0D6D and 0D6E; section-normalized coherence on ringed
sequence sites (blueprint: lem-sf-semilinear-compositor-coherence).

The inverse-image functor denoted `P` in the node is `VaryingRing.G`; its direct-image
functor `S` is `VaryingRing.P`. The forward inverse-image compositor is `gComp.inv`.
All functors, compositors and identity comparisons are those of the specified adjunctions.
The associativity clauses allow independently named intermediate and total composites.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.VaryingRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] gComp pComp jComp gId pId jId adj moduleAdj moduleJAdj
  jAdj

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

attribute [local irreducible] modulePComp modulePId moduleGComp moduleJComp
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.rightDerivedFunctor

-- Fibre-product and section calculations for ordinary direct image.

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (N : Modules R φ X) (n : ℕ) (U : Y.ProEt)
    (x : ((push R φ f).obj N).val.obj (op (n, U))) :
    ((eqToIso (congrArg (push R φ) e)).hom.app N).val.app (op (n, U)) x =
      N.val.map (Prod.mkHom (𝟙 n)
        (eqToHom (congrArg (fun t ↦ (Scheme.proEtaleBaseChange t).obj U) e.symm))).op x := by
  cases e
  change x = N.val.map (𝟙 _) x
  rw [PresheafOfModules.map_id]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_comp_apply
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules R φ X) (n : ℕ) (U : Z.ProEt)
    (x : ((push R φ f ⋙ push R φ g).obj N).val.obj (op (n, U))) :
    ((modulePComp R φ f g).hom.app N).val.app (op (n, U)) x =
      N.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackComp f g).hom.app U)).op x := by
  unfold modulePComp
  exact (modulePComp_existsUnique R φ f g).choose_spec.1 N n U x

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) {N N' : Modules R φ X}
    (a : N ⟶ N') (n : ℕ) (U : Y.ProEt)
    (x : ((push R φ f).obj N).val.obj (op (n, U))) :
    (((push R φ f).map a).val.app (op (n, U))) x =
      a.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U)) x := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_obj_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Modules R φ X)
    (n : ℕ) {U V : Y.ProEt} (a : U ⟶ V)
    (x : ((push R φ f).obj N).val.obj (op (n, V))) :
    (((push R φ f).obj N).val.map (Prod.mkHom (𝟙 n) a).op) x =
      N.val.map (Prod.mkHom (𝟙 n) ((Scheme.proEtaleBaseChange f).map a)).op x := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_coherence
    {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (push R φ f) (modulePComp R φ g h) ≪≫
        modulePComp R φ f (g ≫ h) =
      (Functor.associator (push R φ f) (push R φ g) (push R φ h)).symm ≪≫
        Functor.isoWhiskerRight (modulePComp R φ f g) (push R φ h) ≪≫
        modulePComp R φ (f ≫ g) h ≪≫
        eqToIso (congrArg (push R φ) (Category.assoc f g h)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  rcases U with ⟨n, U⟩
  ext x
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [direct_map_apply R φ h ((modulePComp R φ f g).hom.app N) n U]
  erw [direct_comp_apply R φ f g N n ((Scheme.proEtaleBaseChange h).obj U)]
  erw [direct_comp_apply R φ (f ≫ g) h N n U]
  conv_rhs => erw [direct_transport R φ (Category.assoc f g h) N n U]
  conv_lhs => erw [direct_comp_apply R φ g h ((push R φ f).obj N) n U x]
  conv_lhs => erw [direct_comp_apply R φ f (g ≫ h) N n U]
  conv_lhs => erw [direct_obj_map_apply R φ f N n
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U)]
  apply StrictTower.restriction_pasting N.val
  · apply Prod.hom_ext
    · simp
    · exact StrictTower.site_pasting (P := @WeaklyEtale) (Q := ⊤) f g h U

-- Ordinary inverse-image coherence is the adjoint of the section calculation.

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_coherence
    {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : Modules R φ T) :
    (moduleGComp R φ f (g ≫ h)).hom.app M ≫
        (pull R φ f).map ((moduleGComp R φ g h).hom.app M) =
      (eqToIso (congrArg (pull R φ)
        (Category.assoc f g h).symm)).hom.app M ≫
        (moduleGComp R φ (f ≫ g) h).hom.app M ≫
        (moduleGComp R φ f g).hom.app ((pull R φ h).obj M) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (moduleAdj R φ h) (moduleAdj R φ g) (moduleAdj R φ f)
    (moduleAdj R φ (g ≫ h)) (moduleAdj R φ (f ≫ g))
    (moduleAdj R φ (f ≫ g ≫ h))
    (modulePComp R φ g h) (modulePComp R φ f g)
    ((modulePComp R φ (f ≫ g) h) ≪≫
      eqToIso (congrArg (push R φ) (Category.assoc f g h)))
    (modulePComp R φ f (g ≫ h)) (direct_coherence R φ f g h)
  have ht := StrictTower.mate_transport (pull R φ) (push R φ) (moduleAdj R φ)
    (moduleAdj R φ h) (moduleAdj R φ (f ≫ g)) (Category.assoc f g h)
    (modulePComp R φ (f ≫ g) h)
  rw [ht] at hh
  have hi := NatTrans.congr_app (congrArg Iso.inv hh) M
  simpa only [moduleGComp, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Iso.symm_inv, Category.id_comp, Category.comp_id, Category.assoc, eqToIso.inv, eqToIso.hom]
    using hi.symm

-- Exact derived functors preserve composition and identity pasting.

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem g_coherence {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (M : Derived R φ T) :
    (gComp R φ f (g ≫ h)).hom.app M ≫
        (G R φ f).map ((gComp R φ g h).hom.app M) =
      (eqToIso (congrArg (G R φ) (Category.assoc f g h).symm)).hom.app M ≫
        (gComp R φ (f ≫ g) h).hom.app M ≫
        (gComp R φ f g).hom.app ((G R φ h).obj M) := by
  have ho : moduleGComp R φ f (g ≫ h) ≪≫
      Functor.isoWhiskerRight (moduleGComp R φ g h) (pull R φ f) =
      eqToIso (congrArg (pull R φ) (Category.assoc f g h).symm) ≪≫
        moduleGComp R φ (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (pull R φ h) (moduleGComp R φ f g) := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    exact ordinary_coherence R φ f g h N
  have hh := StrictTower.descend_coherence (pull R φ h) (pull R φ g) (pull R φ f)
    (pull R φ (g ≫ h)) (pull R φ (f ≫ g))
    (pull R φ (f ≫ g ≫ h)) (pull R φ ((f ≫ g) ≫ h))
    (moduleGComp R φ g h) (moduleGComp R φ f g)
    (moduleGComp R φ f (g ≫ h)) (moduleGComp R φ (f ≫ g) h)
    (eqToIso (congrArg (pull R φ) (Category.assoc f g h).symm)) ho
  have hm := NatTrans.congr_app hh M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hm
  rw [congrArg (fun t ↦ t.app M) (derived_transport R φ (Category.assoc f g h).symm)] at hm
  simpa only [gComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
    using hm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_id_apply
    (X : Scheme.{u}) (N : Modules R φ X) (n : ℕ) (U : X.ProEt)
    (x : ((push R φ (𝟙 X)).obj N).val.obj (op (n, U))) :
    ((modulePId R φ X).hom.app N).val.app (op (n, U)) x =
      N.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U)).op x := by
  unfold modulePId
  exact (modulePId_existsUnique R φ X).choose_spec.1 N n U x

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_left_unit
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePComp R φ (𝟙 X) f ≪≫
        eqToIso (congrArg (push R φ) (Category.id_comp f)) =
      Functor.isoWhiskerRight (modulePId R φ X) (push R φ f) ≪≫
        Functor.leftUnitor (push R φ f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  rcases U with ⟨n, U⟩
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [direct_map_apply R φ f ((modulePId R φ X).hom.app N) n U]
  erw [direct_id_apply R φ X N n ((Scheme.proEtaleBaseChange f).obj U)]
  erw [direct_transport R φ (Category.id_comp f) N n U]
  erw [direct_comp_apply R φ (𝟙 X) f N n U]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  apply StrictTower.restriction_eq N.val
  apply Prod.hom_ext
  · simp
  · exact StrictTower.site_left_unit (P := @WeaklyEtale) (Q := ⊤) f U

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_right_unit
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePComp R φ f (𝟙 Y) ≪≫
        eqToIso (congrArg (push R φ) (Category.comp_id f)) =
      Functor.isoWhiskerLeft (push R φ f) (modulePId R φ Y) ≪≫
        Functor.rightUnitor (push R φ f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  rcases U with ⟨n, U⟩
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [direct_id_apply R φ Y ((push R φ f).obj N) n U]
  erw [direct_obj_map_apply R φ f N n
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).inv.app U)]
  erw [direct_transport R φ (Category.comp_id f) N n U]
  erw [direct_comp_apply R φ f (𝟙 Y) N n U]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  apply StrictTower.restriction_eq N.val
  apply Prod.hom_ext
  · simp
  · exact StrictTower.site_right_unit (P := @WeaklyEtale) (Q := ⊤) f U

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules R φ Y) :
    (eqToIso (congrArg (pull R φ) (Category.id_comp f).symm)).hom.app M ≫
        (moduleGComp R φ (𝟙 X) f).hom.app M ≫
        (moduleGId R φ X).hom.app ((pull R φ f).obj M) = 𝟙 _ := by
  have h := Adjunction.leftAdjointCompIso_comp_id (moduleAdj R φ f) (moduleAdj R φ (𝟙 X))
    (modulePComp R φ (𝟙 X) f ≪≫
      eqToIso (congrArg (push R φ) (Category.id_comp f)))
    (modulePId R φ X) (direct_left_unit R φ f)
  rw [StrictTower.mate_transport (pull R φ) (push R φ)
    (moduleAdj R φ) (moduleAdj R φ f) (moduleAdj R φ (𝟙 X))
      (Category.id_comp f) (modulePComp R φ (𝟙 X) f)] at h
  have hi := NatTrans.congr_app (congrArg Iso.inv h) M
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app] at hi
  have he : (eqToIso (congrArg (pull R φ) (Category.id_comp f).symm)).hom.app M ≫
      (moduleGComp R φ (𝟙 X) f).hom.app M =
      𝟙 _ ≫ (moduleGId R φ X).inv.app ((pull R φ f).obj M) := by
    simpa only [moduleGComp, moduleGId, Iso.symm_hom, eqToIso.inv, eqToIso.hom,
      Functor.comp_obj, Functor.id_obj] using hi
  rw [← Category.assoc, he]
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules R φ Y) :
    (eqToIso (congrArg (pull R φ) (Category.comp_id f).symm)).hom.app M ≫
        (moduleGComp R φ f (𝟙 Y)).hom.app M ≫
        (pull R φ f).map ((moduleGId R φ Y).hom.app M) = 𝟙 _ := by
  have h := Adjunction.leftAdjointCompIso_id_comp (moduleAdj R φ (𝟙 Y)) (moduleAdj R φ f)
    (modulePComp R φ f (𝟙 Y) ≪≫
      eqToIso (congrArg (push R φ) (Category.comp_id f)))
    (modulePId R φ Y) (direct_right_unit R φ f)
  rw [StrictTower.mate_transport (pull R φ) (push R φ)
    (moduleAdj R φ) (moduleAdj R φ (𝟙 Y)) (moduleAdj R φ f)
      (Category.comp_id f) (modulePComp R φ f (𝟙 Y))] at h
  have hi := NatTrans.congr_app (congrArg Iso.inv h) M
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app] at hi
  have he : (eqToIso (congrArg (pull R φ) (Category.comp_id f).symm)).hom.app M ≫
      (moduleGComp R φ f (𝟙 Y)).hom.app M =
      𝟙 _ ≫ (pull R φ f).map ((moduleGId R φ Y).inv.app M) := by
    simpa only [moduleGComp, moduleGId, Iso.symm_hom, eqToIso.inv, eqToIso.hom,
      Functor.comp_obj, Functor.id_obj] using hi
  rw [← Category.assoc, he]
  simp [← Functor.map_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem g_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (eqToIso (congrArg (G R φ) (Category.id_comp f).symm)).hom ≫
        (gComp R φ (𝟙 X) f).hom ≫
        Functor.whiskerLeft (G R φ f) (gId R φ X).hom = 𝟙 _ := by
  have ho : eqToIso (congrArg (pull R φ) (Category.id_comp f).symm) ≪≫
      moduleGComp R φ (𝟙 X) f ≪≫
      Functor.isoWhiskerLeft (pull R φ f) (moduleGId R φ X) ≪≫
      Functor.rightUnitor (pull R φ f) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Iso.refl_hom,
      NatTrans.id_app, Functor.comp_obj, Functor.id_obj, Category.comp_id,
      Category.assoc] using ordinary_left_unit R φ f M
  have hh := StrictTower.descend_left_unit (pull R φ f) (pull R φ (𝟙 X ≫ f)) (pull R φ (𝟙 X))
    (eqToIso (congrArg (pull R φ) (Category.id_comp f).symm))
    (moduleGComp R φ (𝟙 X) f) (moduleGId R φ X) ho
  rw [derived_transport R φ (Category.id_comp f).symm] at hh
  simpa only [gComp, gId, moduleGId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
    using hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem g_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (eqToIso (congrArg (G R φ) (Category.comp_id f).symm)).hom ≫
        (gComp R φ f (𝟙 Y)).hom ≫
        Functor.whiskerRight (gId R φ Y).hom (G R φ f) = 𝟙 _ := by
  have ho : eqToIso (congrArg (pull R φ) (Category.comp_id f).symm) ≪≫
      moduleGComp R φ f (𝟙 Y) ≪≫
      Functor.isoWhiskerRight (moduleGId R φ Y) (pull R φ f) ≪≫
      Functor.leftUnitor (pull R φ f) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.refl_hom,
      NatTrans.id_app, Functor.comp_obj, Functor.id_obj, Category.comp_id,
      Category.assoc] using ordinary_right_unit R φ f M
  have hh := StrictTower.descend_right_unit (pull R φ f) (pull R φ (f ≫ 𝟙 Y)) (pull R φ (𝟙 Y))
    (eqToIso (congrArg (pull R φ) (Category.comp_id f).symm))
    (moduleGComp R φ f (𝟙 Y)) (moduleGId R φ Y) ho
  rw [derived_transport R φ (Category.comp_id f).symm] at hh
  simpa only [gComp, gId, moduleGId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
    using hh

-- Conjugation transfers the inverse-image equations to derived direct image.

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def gCompEq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    G R φ h ≅ G R φ g ⋙ G R φ f :=
  eqToIso (congrArg (G R φ) w.symm) ≪≫ gComp R φ f g

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem gCompEq_inv_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    (M : Derived R φ Z) :
    (gCompEq R φ f g h w).inv.app M =
      (gComp R φ f g).inv.app M ≫ (eqToIso (congrArg (G R φ) w)).hom.app M := by
  subst h
  simp only [gCompEq, eqToIso_refl, Iso.refl_trans, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem gCompEq_coherence {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (abc : W ⟶ Z)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) :
    gCompEq R φ a bc abc hr ≪≫
        Functor.isoWhiskerRight (gCompEq R φ b c bc hbc) (G R φ a) =
      gCompEq R φ ab c abc hl ≪≫
        Functor.isoWhiskerLeft (G R φ c) (gCompEq R φ a b ab hab) := by
  subst ab bc
  cases hr
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [gCompEq, eqToIso_refl, Iso.refl_trans, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] using g_coherence R φ a b c M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem p_transport {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    pComp R φ f g ≪≫ eqToIso (congrArg (P R φ) w) =
      conjugateIsoEquiv ((adj R φ g).comp (adj R φ f)) (adj R φ h)
        (gCompEq R φ f g h w) := by
  subst h
  simp only [gCompEq, eqToIso_refl, Iso.refl_trans, Iso.trans_refl]
  unfold pComp
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem p_transport_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    conjugateEquiv ((adj R φ g).comp (adj R φ f)) (adj R φ h)
        (gCompEq R φ f g h w).hom =
      (pComp R φ f g ≪≫ eqToIso (congrArg (P R φ) w)).hom := by
  exact (congrArg Iso.hom (p_transport R φ f g h w)).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem conjugate_unit_right {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R₀ : D ⥤ C} {I RI : C ⥤ C}
    (a : F ⊣ R₀) (b : I ⊣ RI) (e : I ≅ 𝟭 C) (k : F ≅ I ⋙ F)
    (h : k ≪≫ Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F = Iso.refl F) :
    conjugateIsoEquiv (b.comp a) a k =
      Functor.isoWhiskerLeft R₀ (conjugateIsoEquiv b Adjunction.id e.symm) ≪≫
        Functor.rightUnitor R₀ := by
  have hk : k = (Functor.leftUnitor F).symm ≪≫ Functor.isoWhiskerRight e.symm F := by
    apply Iso.ext
    have hh := congrArg Iso.hom h
    change k.hom ≫ (Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F).hom = 𝟙 _ at hh
    have hi := (Iso.comp_hom_eq_id
      (Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F)).1 hh
    simpa only [Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerRight_symm,
      Iso.symm_hom, Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom] using hi
  rw [hk, conjugateIsoEquiv_trans (b.comp a) (Adjunction.id.comp a) a,
    conjugateIsoEquiv_isoWhiskerRight b Adjunction.id a,
    conjugateIsoEquiv_iso_symm a (Adjunction.id.comp a),
    conjugateIsoEquiv_leftUnitor, Iso.symm_symm_eq]

-- Open extension is treated by the same adjoint and exact-localization argument.

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem jCongr_eq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (e : f = g) :
    jCongr R φ e = eqToIso (congrArg
      (fun a : {a : X ⟶ Y // IsOpenImmersion a} ↦ @J R φ _ _ a.1 a.2)
      (@Subtype.ext (X ⟶ Y) (fun a ↦ IsOpenImmersion a)
        ⟨f, inferInstance⟩ ⟨g, inferInstance⟩ e)) := by
  cases e
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_j_coherence {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h] :
    Functor.isoWhiskerLeft (extension R φ f) (moduleJComp R φ g h) ≪≫
        moduleJComp R φ f (g ≫ h) =
      (Functor.associator (extension R φ f) (extension R φ g) (extension R φ h)).symm ≪≫
        Functor.isoWhiskerRight (moduleJComp R φ f g) (extension R φ h) ≪≫
        moduleJComp R φ (f ≫ g) h ≪≫ moduleJCongr R φ (Category.assoc f g h) := by
  have ho : Functor.isoWhiskerLeft (pull R φ h) (moduleGComp R φ f g).symm ≪≫
        (moduleGComp R φ (f ≫ g) h).symm ≪≫
        eqToIso (congrArg (pull R φ) (Category.assoc f g h)) =
      (Functor.associator (pull R φ h) (pull R φ g) (pull R φ f)).symm ≪≫
        Functor.isoWhiskerRight (moduleGComp R φ g h).symm (pull R φ f) ≪≫
        (moduleGComp R φ f (g ≫ h)).symm := by
    have hg : moduleGComp R φ f (g ≫ h) ≪≫
        Functor.isoWhiskerRight (moduleGComp R φ g h) (pull R φ f) =
        eqToIso (congrArg (pull R φ) (Category.assoc f g h).symm) ≪≫
          moduleGComp R φ (f ≫ g) h ≪≫
          Functor.isoWhiskerLeft (pull R φ h) (moduleGComp R φ f g) := by
      apply Iso.ext
      apply NatTrans.ext
      funext M
      exact ordinary_coherence R φ f g h M
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have hh := congrArg (fun q ↦ q.inv.app M) hg
    simpa only [Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.trans_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app, Iso.symm_hom,
      Category.id_comp, eqToIso.hom, eqToIso.inv, Category.assoc] using hh.symm
  have hh := Adjunction.leftAdjointCompIso_assoc
    (moduleJAdj R φ f) (moduleJAdj R φ g) (moduleJAdj R φ h)
    (moduleJAdj R φ (f ≫ g)) (moduleJAdj R φ (g ≫ h))
    (moduleJAdj R φ (f ≫ g ≫ h))
    (moduleGComp R φ f g).symm (moduleGComp R φ g h).symm
    (moduleGComp R φ f (g ≫ h)).symm
    ((moduleGComp R φ (f ≫ g) h).symm ≪≫
      eqToIso (congrArg (pull R φ) (Category.assoc f g h))) ho
  let L : {a : X ⟶ T // IsOpenImmersion a} → Modules R φ X ⥤ Modules R φ T :=
    fun a ↦ @extension R φ _ _ a.1 a.2
  let Q : {a : X ⟶ T // IsOpenImmersion a} → Modules R φ T ⥤ Modules R φ X :=
    fun a ↦ pull R φ a.1
  let a : ∀ t, L t ⊣ Q t := fun t ↦ @moduleJAdj R φ _ _ t.1 t.2
  have ht := StrictTower.mate_transport L Q a (moduleJAdj R φ (f ≫ g)) (moduleJAdj R φ h)
    (Subtype.ext (Category.assoc f g h) :
      (⟨(f ≫ g) ≫ h, inferInstance⟩ : {a : X ⟶ T // IsOpenImmersion a}) =
      ⟨f ≫ g ≫ h, inferInstance⟩) (moduleGComp R φ (f ≫ g) h).symm
  have ht' : Adjunction.leftAdjointCompIso
      (moduleJAdj R φ (f ≫ g)) (moduleJAdj R φ h) (moduleJAdj R φ (f ≫ g ≫ h))
      ((moduleGComp R φ (f ≫ g) h).symm ≪≫
        eqToIso (congrArg (pull R φ) (Category.assoc f g h))) =
      moduleJComp R φ (f ≫ g) h ≪≫ moduleJCongr R φ (Category.assoc f g h) := by
    simpa only [moduleJComp, moduleJCongr, L, Q, a] using ht
  rw [ht'] at hh
  simpa only [moduleJComp, Iso.trans_assoc] using hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem j_coherence {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h] :
    Functor.isoWhiskerLeft (J R φ f) (jComp R φ g h) ≪≫ jComp R φ f (g ≫ h) =
      (Functor.associator (J R φ f) (J R φ g) (J R φ h)).symm ≪≫
        Functor.isoWhiskerRight (jComp R φ f g) (J R φ h) ≪≫
        jComp R φ (f ≫ g) h ≪≫ jCongr R φ (Category.assoc f g h) := by
  have ho : (moduleJComp R φ (f ≫ g) h).symm ≪≫
      Functor.isoWhiskerRight (moduleJComp R φ f g).symm (extension R φ h) =
      moduleJCongr R φ (Category.assoc f g h) ≪≫
        (moduleJComp R φ f (g ≫ h)).symm ≪≫
        Functor.isoWhiskerLeft (extension R φ f) (moduleJComp R φ g h).symm := by
    have hh := congrArg Iso.inv (ordinary_j_coherence R φ f g h)
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have hm := congr_app hh M
    apply (cancel_epi ((moduleJCongr R φ (Category.assoc f g h)).inv.app M)).1
    simpa only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app, Iso.symm_inv,
      Iso.symm_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.comp_id, Category.assoc, Iso.inv_hom_id_app_assoc] using hm.symm
  have hh := StrictTower.descend_coherence (extension R φ f) (extension R φ g) (extension R φ h)
    (extension R φ (f ≫ g)) (extension R φ (g ≫ h))
    (extension R φ ((f ≫ g) ≫ h)) (extension R φ (f ≫ g ≫ h))
    (moduleJComp R φ f g).symm (moduleJComp R φ g h).symm
    (moduleJComp R φ (f ≫ g) h).symm (moduleJComp R φ f (g ≫ h)).symm
    (moduleJCongr R φ (Category.assoc f g h)) ho
  rw [derivedJ_transport R φ (Category.assoc f g h)] at hh
  apply (Iso.symm_bijective).injective
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hm := congr_app hh M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapDerivedCategoryNatIso_symm] at hm
  apply (cancel_epi ((jCongr R φ (Category.assoc f g h)).hom.app M)).1
  simpa only [jComp, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
    Functor.associator_hom_app, Category.comp_id, Category.assoc,
    Iso.hom_inv_id_app_assoc] using hm.symm

-- Identify the localized ordinary open identity with the specified derived one.

attribute [local irreducible] moduleGId moduleJId derivedJId

-- The identity comparison is checked on localized complexes.

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_g_left {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleGComp R φ (𝟙 X) f).inv ≫
        (eqToIso (congrArg (pull R φ) (Category.id_comp f))).hom =
      Functor.whiskerLeft (pull R φ f) (moduleGId R φ X).hom := by
  apply (cancel_epi (moduleGComp R φ (𝟙 X) f).hom).1
  rw [Iso.hom_inv_id_assoc]
  apply NatTrans.ext
  funext M
  have hh := ordinary_left_unit R φ f M
  apply (cancel_epi
    ((eqToIso (congrArg (pull R φ) (Category.id_comp f).symm)).hom.app M)).1
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
    eqToIso.hom, eqToHom_app, eqToHom_trans, eqToHom_refl,
    NatTrans.id_app, Category.id_comp, Category.comp_id]
      using hh.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_g_right {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleGComp R φ f (𝟙 Y)).inv ≫
        (eqToIso (congrArg (pull R φ) (Category.comp_id f))).hom =
      Functor.whiskerRight (moduleGId R φ Y).hom (pull R φ f) := by
  apply (cancel_epi (moduleGComp R φ f (𝟙 Y)).hom).1
  rw [Iso.hom_inv_id_assoc]
  apply NatTrans.ext
  funext M
  have hh := ordinary_right_unit R φ f M
  apply (cancel_epi
    ((eqToIso (congrArg (pull R φ) (Category.comp_id f).symm)).hom.app M)).1
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc,
    eqToIso.hom, eqToHom_app, eqToHom_trans, eqToHom_refl,
    NatTrans.id_app, Category.id_comp, Category.comp_id]
      using hh.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_j_left {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (moduleJComp R φ (𝟙 X) f).inv ≫
        Functor.whiskerRight (moduleJId R φ X).hom (extension R φ f) =
      (moduleJCongr R φ (Category.id_comp f)).hom := by
  let K := {t : X ⟶ Y // IsOpenImmersion t}
  let L : K → Modules R φ X ⥤ Modules R φ Y := fun t ↦ @extension R φ _ _ t.1 t.2
  let Q : K → Modules R φ Y ⥤ Modules R φ X := fun t ↦ pull R φ t.1
  let a : ∀ t : K, L t ⊣ Q t := fun t ↦ @moduleJAdj R φ _ _ t.1 t.2
  have hd : (moduleGComp R φ (𝟙 X) f).symm ≪≫
      eqToIso (congrArg (pull R φ) (Category.id_comp f)) =
      Functor.isoWhiskerLeft (pull R φ f) (moduleGId R φ X) ≪≫
        Functor.rightUnitor (pull R φ f) := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
      Category.comp_id] using congr_app (ordinary_g_left R φ f) M
  unfold moduleJComp moduleJId
  exact StrictTower.leftAdjoint_unit_right L Q a (moduleJAdj R φ (𝟙 X))
    (moduleGId R φ X)
    (Subtype.ext (Category.id_comp f) :
      (⟨𝟙 X ≫ f, inferInstance⟩ : K) = ⟨f, inferInstance⟩)
    (moduleGComp R φ (𝟙 X) f).symm hd

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinary_j_right {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (moduleJComp R φ f (𝟙 Y)).inv ≫
        Functor.whiskerLeft (extension R φ f) (moduleJId R φ Y).hom =
      (moduleJCongr R φ (Category.comp_id f)).hom := by
  let K := {t : X ⟶ Y // IsOpenImmersion t}
  let L : K → Modules R φ X ⥤ Modules R φ Y := fun t ↦ @extension R φ _ _ t.1 t.2
  let Q : K → Modules R φ Y ⥤ Modules R φ X := fun t ↦ pull R φ t.1
  let a : ∀ t : K, L t ⊣ Q t := fun t ↦ @moduleJAdj R φ _ _ t.1 t.2
  have hd : (moduleGComp R φ f (𝟙 Y)).symm ≪≫
      eqToIso (congrArg (pull R φ) (Category.comp_id f)) =
      Functor.isoWhiskerRight (moduleGId R φ Y) (pull R φ f) ≪≫
        Functor.leftUnitor (pull R φ f) := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
      Category.comp_id] using congr_app (ordinary_g_right R φ f) M
  unfold moduleJComp moduleJId
  exact StrictTower.leftAdjoint_unit_left L Q a (moduleJAdj R φ (𝟙 Y))
    (moduleGId R φ Y)
    (Subtype.ext (Category.comp_id f) :
      (⟨f ≫ 𝟙 Y, inferInstance⟩ : K) = ⟨f, inferInstance⟩)
    (moduleGComp R φ f (𝟙 Y)).symm hd

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem j_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Derived R φ X) :
    (jComp R φ (𝟙 X) f).hom.app M ≫
        (jCongr R φ (Category.id_comp f)).hom.app M =
      (J R φ f).map ((jId R φ X).hom.app M) := by
  have ht := StrictTower.derived_unit_right (extension R φ f) (extension R φ (𝟙 X ≫ f))
    (extension R φ (𝟙 X)) (moduleJComp R φ (𝟙 X) f).symm
    (moduleJId R φ X) (moduleJCongr R φ (Category.id_comp f)) (ordinary_j_left R φ f)
  rw [Functor.mapDerivedCategoryNatIso_symm, derivedJ_transport] at ht
  have hh : (jComp R φ (𝟙 X) f).inv ≫
      Functor.whiskerRight (derivedJId R φ X).hom (J R φ f) =
      (jCongr R φ (Category.id_comp f)).hom := by
    simpa only [jComp, derivedJId, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
      Functor.whiskerRight_comp, Category.assoc] using ht
  rw [← jId_eq] at hh
  have hm := congr_app hh M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hm
  apply (cancel_epi ((jComp R φ (𝟙 X) f).inv.app M)).1
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using hm.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem j_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Derived R φ X) :
    (jComp R φ f (𝟙 Y)).hom.app M ≫
        (jCongr R φ (Category.comp_id f)).hom.app M =
      (jId R φ Y).hom.app ((J R φ f).obj M) := by
  have ht := StrictTower.derived_unit_left (extension R φ f) (extension R φ (f ≫ 𝟙 Y))
    (extension R φ (𝟙 Y)) (moduleJComp R φ f (𝟙 Y)).symm
    (moduleJId R φ Y) (moduleJCongr R φ (Category.comp_id f)) (ordinary_j_right R φ f)
  rw [Functor.mapDerivedCategoryNatIso_symm, derivedJ_transport] at ht
  have hh : (jComp R φ f (𝟙 Y)).inv ≫
      Functor.whiskerLeft (J R φ f) (derivedJId R φ Y).hom =
      (jCongr R φ (Category.comp_id f)).hom := by
    simpa only [jComp, derivedJId, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
      Functor.whiskerLeft_comp, Category.assoc] using ht
  rw [← jId_eq] at hh
  have hm := congr_app hh M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hm
  apply (cancel_epi ((jComp R φ f (𝟙 Y)).inv.app M)).1
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using hm.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coherence_clause_1 :
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ T),
      (G R φ f).map ((gComp R φ g h).inv.app M ≫
          (eqToIso (congrArg (G R φ) egh)).hom.app M) ≫
        (gComp R φ f l).inv.app M ≫ (eqToIso (congrArg (G R φ) efl)).hom.app M =
      (gComp R φ f g).inv.app ((G R φ h).obj M) ≫
        (eqToIso (congrArg (G R φ) efg)).hom.app ((G R φ h).obj M) ≫
        (gComp R φ k h).inv.app M ≫ (eqToIso (congrArg (G R φ) ekh)).hom.app M) := by
  intro X Y Z T f g h k l m efg egh ekh efl M
  have hh := congrArg (fun q ↦ q.inv.app M)
    (gCompEq_coherence R φ f g h k l m efg egh ekh efl)
  simp only [Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, gCompEq_inv_app] at hh
  simpa only [Functor.map_comp, Category.assoc] using hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coherence_clause_2 :
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ X),
      (P R φ h).map ((pComp R φ f g).hom.app M ≫
          (eqToIso (congrArg (P R φ) efg)).hom.app M) ≫
        (pComp R φ k h).hom.app M ≫ (eqToIso (congrArg (P R φ) ekh)).hom.app M =
      (pComp R φ g h).hom.app ((P R φ f).obj M) ≫
        (eqToIso (congrArg (P R φ) egh)).hom.app ((P R φ f).obj M) ≫
        (pComp R φ f l).hom.app M ≫ (eqToIso (congrArg (P R φ) efl)).hom.app M) := by
  intro X Y Z T f g h k l m efg egh ekh efl M
  have hg := congrArg Iso.hom
    (gCompEq_coherence R φ f g h k l m efg egh ekh efl)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom] at hg
  have hh := StrictTower.conjugate_triangle_assoc (adj R φ h) (adj R φ g) (adj R φ f)
    (adj R φ l) (adj R φ k) (adj R φ m)
    (gCompEq R φ g h l egh) (gCompEq R φ f g k efg)
    (gCompEq R φ k h m ekh) (gCompEq R φ f l m efl) hg.symm
  rw [p_transport_hom R φ g h l egh, p_transport_hom R φ f g k efg,
    p_transport_hom R φ k h m ekh, p_transport_hom R φ f l m efl] at hh
  have hm := NatTrans.congr_app hh M
  simpa only [conjugateIsoEquiv_apply_hom, Iso.trans_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using hm.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coherence_clause_3 :
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion m]
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ X),
      (J R φ h).map ((jComp R φ f g).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Z // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Z) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ g, inferInstance⟩ ⟨k, inferInstance⟩ efg))).hom.app M) ≫
        (jComp R φ k h).hom.app M ≫
        (eqToIso (congrArg
          (fun a : {a : X ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (X ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨k ≫ h, inferInstance⟩ ⟨m, inferInstance⟩ ekh))).hom.app M =
      (jComp R φ g h).hom.app ((J R φ f).obj M) ≫
        (eqToIso (congrArg
          (fun a : {a : Y ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (Y ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨g ≫ h, inferInstance⟩ ⟨l, inferInstance⟩ egh))).hom.app
          ((J R φ f).obj M) ≫
        (jComp R φ f l).hom.app M ≫
        (eqToIso (congrArg
          (fun a : {a : X ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (X ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ l, inferInstance⟩ ⟨m, inferInstance⟩ efl))).hom.app M) := by
  intro X Y Z T f g h k l m _ _ _ _ _ _ efg egh ekh efl M
  subst k l
  cases efl
  have hh := congrArg (fun q ↦ q.hom.app M) (j_coherence R φ f g h)
  simpa only [jCongr_eq, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Functor.associator_inv_app, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Category.id_comp, Functor.map_id, Category.assoc] using hh.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coherence_clause_4 :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ Y),
      (gComp R φ (𝟙 X) f).inv.app M ≫
          (eqToIso (congrArg (G R φ) (Category.id_comp f))).hom.app M =
        (gId R φ X).hom.app ((G R φ f).obj M)) := by
  intro X Y f M
  have hu : Functor.whiskerLeft (G R φ f) (gId R φ X).hom =
      (eqToIso (congrArg (G R φ) (Category.id_comp f).symm) ≪≫
        gComp R φ (𝟙 X) f).inv := (Iso.hom_comp_eq_id
    (eqToIso (congrArg (G R φ) (Category.id_comp f).symm) ≪≫
      gComp R φ (𝟙 X) f)).1 (by
        simpa only [Iso.trans_hom, Category.assoc] using g_left_unit R φ f)
  have hm := congr_app hu M
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    eqToIso.inv, eqToIso.hom] using hm.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coherence_clause_5 :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ Y),
      (gComp R φ f (𝟙 Y)).inv.app M ≫
          (eqToIso (congrArg (G R φ) (Category.comp_id f))).hom.app M =
        (G R φ f).map ((gId R φ Y).hom.app M)) := by
  intro X Y f M
  have hu : Functor.whiskerRight (gId R φ Y).hom (G R φ f) =
      (eqToIso (congrArg (G R φ) (Category.comp_id f).symm) ≪≫
        gComp R φ f (𝟙 Y)).inv := (Iso.hom_comp_eq_id
    (eqToIso (congrArg (G R φ) (Category.comp_id f).symm) ≪≫
      gComp R φ f (𝟙 Y))).1 (by
        simpa only [Iso.trans_hom, Category.assoc] using g_right_unit R φ f)
  have hm := congr_app hu M
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    eqToIso.inv, eqToIso.hom] using hm.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coherence_clause_6 :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ X),
      (pComp R φ (𝟙 X) f).hom.app M ≫
          (eqToIso (congrArg (P R φ) (Category.id_comp f))).hom.app M =
        (P R φ f).map ((pId R φ X).hom.app M)) := by
  intro X Y f M
  have ho : gCompEq R φ (𝟙 X) f f (Category.id_comp f) ≪≫
      Functor.isoWhiskerLeft (G R φ f) (gId R φ X) ≪≫
      Functor.rightUnitor (G R φ f) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    simpa only [gCompEq, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
      Category.comp_id, Category.assoc, Iso.refl_hom, NatTrans.id_app] using
      congr_app (g_left_unit R φ f) N
  have hh := StrictTower.conjugate_unit (adj R φ f) (adj R φ (𝟙 X)) (gId R φ X)
    (gCompEq R φ (𝟙 X) f f (Category.id_comp f)) ho
  rw [← p_transport] at hh
  have hm := congrArg (fun q ↦ q.hom.app M) hh
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Category.comp_id,
    conjugateIsoEquiv_iso_symm, pId, Functor.comp_obj, Functor.id_obj] using hm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coherence_clause_7 :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ X),
      (pComp R φ f (𝟙 Y)).hom.app M ≫
          (eqToIso (congrArg (P R φ) (Category.comp_id f))).hom.app M =
        (pId R φ Y).hom.app ((P R φ f).obj M)) := by
  intro X Y f M
  have ho : gCompEq R φ f (𝟙 Y) f (Category.comp_id f) ≪≫
      Functor.isoWhiskerRight (gId R φ Y) (G R φ f) ≪≫
      Functor.leftUnitor (G R φ f) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    simpa only [gCompEq, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
      Category.comp_id, Category.assoc, Iso.refl_hom, NatTrans.id_app] using
      congr_app (g_right_unit R φ f) N
  have hh := conjugate_unit_right (adj R φ f) (adj R φ (𝟙 Y)) (gId R φ Y)
    (gCompEq R φ f (𝟙 Y) f (Category.comp_id f)) ho
  rw [← p_transport] at hh
  have hm := congrArg (fun q ↦ q.hom.app M) hh
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.comp_id,
    conjugateIsoEquiv_iso_symm, pId, Functor.comp_obj, Functor.id_obj] using hm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coherence_clause_8 :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Derived R φ X),
      (jComp R φ (𝟙 X) f).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Y // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Y) (fun a ↦ IsOpenImmersion a)
              ⟨𝟙 X ≫ f, inferInstance⟩ ⟨f, inferInstance⟩ (Category.id_comp f)))).hom.app M =
        (J R φ f).map ((jId R φ X).hom.app M)) := by
  intro X Y f _ M
  simpa only [jCongr_eq] using j_left_unit R φ f M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coherence_clause_9 :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Derived R φ X),
      (jComp R φ f (𝟙 Y)).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Y // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Y) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ 𝟙 Y, inferInstance⟩ ⟨f, inferInstance⟩ (Category.comp_id f)))).hom.app M =
        (jId R φ Y).hom.app ((J R φ f).obj M)) := by
  intro X Y f _ M
  simpa only [jCongr_eq] using j_right_unit R φ f M

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Associativity and both unit laws for the three normalized semilinear compositors,
including transport along arbitrary equalities identifying intermediate and total maps.
Source: Stacks Project, Tags 0D6D, 0D6E, 0B65, 0DV0 and 04VG
(blueprint: lem-sf-semilinear-compositor-coherence).

Proof:
1. The two ordinary direct-image pastings restrict sections along the same map of
iterated fibre products: their projections agree. The fibre-product universal property
(def-pc-fibre-product) identifies these maps. The same projection check identifies
identity composition with the graph-normalized modulePId.
2. Apply lem-trf-adjoint-composition-coherence to the ordinary inverse-image adjoints,
using the inverses of these section comparisons on the right adjoints. The composite
adjunction is def-weil-pbc-composite-adjunction. Unit-compatible uniqueness from
situation-conventions identifies the resulting comparisons with
moduleGComp, hence proves their associativity.
3. For identities, insert the explicit composite-adjunction unit. Naturality of the
ordinary unit and modulePId makes each whiskered identity comparison satisfy the
same unit equation as moduleGComp. Unit-compatible uniqueness gives both unit laws.
No two distinct adjunction structures are identified.
4. Localize the exact ordinary inverse images termwise, using
situation-conventions. After postcomposition by the
factorization isomorphism, both pastings reduce to the corresponding ordinary pastings;
naturality cancels the intermediate factorization maps. They agree by steps 2 and 3.
Part (3) of lem-weil-pbc-localization-universal-property promotes equality on every
localized complex to equality on the entire unbounded derived category.
5. Invert inverse-image coherence and take its conjugate under the fixed derived
adjunctions (def-weil-pbc-adjunction-conjugate). Composition of conjugates and
lem-weil-pbc-mate-pasting (2) identify the two pastings with the pComp pastings.
Apply the same argument to inverse unit equations, using mate-pasting (4) for identities.
6. Apply lem-trf-adjoint-composition-coherence to ordinary open extension left adjoints
and inverse-image right adjoints, using step 2 for the right-adjoint hypothesis.
Unit-compatible uniqueness identifies the result with moduleJComp. Repeat step 3's
unit calculation for these open adjunctions to obtain both ordinary open unit laws.
7. Localize these exact open functors as in step 4. Ordinary open coherence becomes
jComp coherence by the factorization isomorphisms and localization extensionality.
Localized units have the same unit equation as jId; unit-compatible uniqueness
identifies them with this specified derived identity normalization.
8. Eliminate the supplied equalities of intermediate and total scheme maps, one at
a time. The transports then become identities and the claims are precisely the
coherence and unit equations already obtained. Proof irrelevance identifies the
open-immersion instances under this transport. -/
theorem semilinear_compositor_coherence
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n) :
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ T),
      (G R φ f).map ((gComp R φ g h).inv.app M ≫
          (eqToIso (congrArg (G R φ) egh)).hom.app M) ≫
        (gComp R φ f l).inv.app M ≫ (eqToIso (congrArg (G R φ) efl)).hom.app M =
      (gComp R φ f g).inv.app ((G R φ h).obj M) ≫
        (eqToIso (congrArg (G R φ) efg)).hom.app ((G R φ h).obj M) ≫
        (gComp R φ k h).inv.app M ≫ (eqToIso (congrArg (G R φ) ekh)).hom.app M) ∧
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ X),
      (P R φ h).map ((pComp R φ f g).hom.app M ≫
          (eqToIso (congrArg (P R φ) efg)).hom.app M) ≫
        (pComp R φ k h).hom.app M ≫ (eqToIso (congrArg (P R φ) ekh)).hom.app M =
      (pComp R φ g h).hom.app ((P R φ f).obj M) ≫
        (eqToIso (congrArg (P R φ) egh)).hom.app ((P R φ f).obj M) ≫
        (pComp R φ f l).hom.app M ≫ (eqToIso (congrArg (P R φ) efl)).hom.app M) ∧
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (k : X ⟶ Z) (l : Y ⟶ T) (m : X ⟶ T)
      [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion m]
      (efg : f ≫ g = k) (egh : g ≫ h = l) (ekh : k ≫ h = m) (efl : f ≫ l = m)
      (M : Derived R φ X),
      (J R φ h).map ((jComp R φ f g).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Z // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Z) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ g, inferInstance⟩ ⟨k, inferInstance⟩ efg))).hom.app M) ≫
        (jComp R φ k h).hom.app M ≫
        (eqToIso (congrArg
          (fun a : {a : X ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (X ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨k ≫ h, inferInstance⟩ ⟨m, inferInstance⟩ ekh))).hom.app M =
      (jComp R φ g h).hom.app ((J R φ f).obj M) ≫
        (eqToIso (congrArg
          (fun a : {a : Y ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (Y ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨g ≫ h, inferInstance⟩ ⟨l, inferInstance⟩ egh))).hom.app
          ((J R φ f).obj M) ≫
        (jComp R φ f l).hom.app M ≫
        (eqToIso (congrArg
          (fun a : {a : X ⟶ T // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
          (@Subtype.ext (X ⟶ T) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ l, inferInstance⟩ ⟨m, inferInstance⟩ efl))).hom.app M) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ Y),
      (gComp R φ (𝟙 X) f).inv.app M ≫
          (eqToIso (congrArg (G R φ) (Category.id_comp f))).hom.app M =
        (gId R φ X).hom.app ((G R φ f).obj M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ Y),
      (gComp R φ f (𝟙 Y)).inv.app M ≫
          (eqToIso (congrArg (G R φ) (Category.comp_id f))).hom.app M =
        (G R φ f).map ((gId R φ Y).hom.app M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ X),
      (pComp R φ (𝟙 X) f).hom.app M ≫
          (eqToIso (congrArg (P R φ) (Category.id_comp f))).hom.app M =
        (P R φ f).map ((pId R φ X).hom.app M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived R φ X),
      (pComp R φ f (𝟙 Y)).hom.app M ≫
          (eqToIso (congrArg (P R φ) (Category.comp_id f))).hom.app M =
        (pId R φ Y).hom.app ((P R φ f).obj M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Derived R φ X),
      (jComp R φ (𝟙 X) f).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Y // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Y) (fun a ↦ IsOpenImmersion a)
              ⟨𝟙 X ≫ f, inferInstance⟩ ⟨f, inferInstance⟩ (Category.id_comp f)))).hom.app M =
        (J R φ f).map ((jId R φ X).hom.app M)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Derived R φ X),
      (jComp R φ f (𝟙 Y)).hom.app M ≫
          (eqToIso (congrArg
            (fun a : {a : X ⟶ Y // IsOpenImmersion a} ↦ @J R φ _ _ a.val a.property)
            (@Subtype.ext (X ⟶ Y) (fun a ↦ IsOpenImmersion a)
              ⟨f ≫ 𝟙 Y, inferInstance⟩ ⟨f, inferInstance⟩ (Category.comp_id f)))).hom.app M =
        (jId R φ Y).hom.app ((J R φ f).obj M)) := by
  exact ⟨coherence_clause_1 R φ, coherence_clause_2 R φ, coherence_clause_3 R φ,
    coherence_clause_4 R φ, coherence_clause_5 R φ, coherence_clause_6 R φ,
    coherence_clause_7 R φ, coherence_clause_8 R φ, coherence_clause_9 R φ⟩

end AlgebraicGeometry.ProEtale.VaryingRing
