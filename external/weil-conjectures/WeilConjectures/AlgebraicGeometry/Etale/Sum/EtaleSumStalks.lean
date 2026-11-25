/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

set_option linter.privateModule false

/-!
# Geometric stalks of étale sum extension

Source: Stacks Project, Tag 03S5, `proposition-describe-jshriek`, and Tag 0710,
`lemma-stalk-j-shriek` (blueprint: lem-amb-etale-sum-stalks).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

namespace AlgebraicGeometry

namespace Etale.SumStalks

variable {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
  (A : Type (u + 1)) [CommRing A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)

private local instance moduleLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} A) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

private abbrev base : U.Etale ⥤ X.Etale := MorphismProperty.Over.map ⊤ (inferInstance : Etale f)

private noncomputable abbrev sum (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    ModuleCat.{u + 1} A :=
  ModuleCat.of A (⨁ (z : Over.mk x ⟶ Over.mk f),
    ((Scheme.pointSmallEtale z.left).presheafFiber (A := ModuleCat.{u + 1} A)).obj F)

private noncomputable abbrev presheaf (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A :=
  (base f).op.lan.obj F

-- The Kan-extension and stalk universal properties detect equality on section germs.
private lemma hom_ext (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    {T : ModuleCat.{u + 1} A}
    {g h : ((Scheme.pointSmallEtale x).presheafFiber (A := ModuleCat.{u + 1} A)).obj
      (presheaf f A F) ⟶ T}
    (he : ∀ (W : U.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj ((base f).obj W)),
      ((base f).op.lanUnit.app F).app (op W) ≫
        (Scheme.pointSmallEtale x).toPresheafFiber (A := ModuleCat.{u + 1} A)
          ((base f).obj W) v (presheaf f A F) ≫ g =
      ((base f).op.lanUnit.app F).app (op W) ≫
        (Scheme.pointSmallEtale x).toPresheafFiber (A := ModuleCat.{u + 1} A)
          ((base f).obj W) v (presheaf f A F) ≫ h) : g = h := by
  apply ((Scheme.pointSmallEtale x).skyscraperPresheafHomEquiv (A := ModuleCat.{u + 1} A)).injective
  apply Functor.hom_ext_of_isLeftKanExtension _ ((base f).op.lanUnit.app F)
  apply NatTrans.ext
  funext W
  apply Pi.hom_ext
  intro v
  simpa using he W.unop v

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def forgetPoint (z : Over.mk x ⟶ Over.mk f) (W : U.Etale)
    (w : (Scheme.pointSmallEtale z.left).fiber.obj W) :
    (Scheme.pointSmallEtale x).fiber.obj ((base f).obj W) :=
  Over.homMk w.left (by
    change w.left ≫ (W.hom ≫ f) = x
    have hw : w.left ≫ W.hom = z.left := Over.w w
    rw [← Category.assoc, hw]
    exact Over.w z)

open Classical in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def forwardFamily
    (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) (W : U.Etale)
    (v : (Scheme.pointSmallEtale x).fiber.obj ((base f).obj W)) :
    F.obj (op W) ⟶ sum f A x F :=
  (Scheme.pointSmallEtale (v.left ≫ W.hom)).toPresheafFiber W
    (Over.homMk v.left) F ≫
      ModuleCat.ofHom (DirectSum.lof A _
        (fun z : Over.mk x ⟶ Over.mk f ↦
          ((Scheme.pointSmallEtale z.left).presheafFiber (A := ModuleCat.{u + 1} A)).obj F)
        (v ≫ Over.homMk W.hom))

open Classical in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma forwardFamily_eq (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (z : Over.mk x ⟶ Over.mk f) (W : U.Etale)
    (w : (Scheme.pointSmallEtale z.left).fiber.obj W) :
    forwardFamily f A x F W (forgetPoint f x z W w) =
      (Scheme.pointSmallEtale z.left).toPresheafFiber W w F ≫
        ModuleCat.ofHom (DirectSum.lof A _
          (fun z : Over.mk x ⟶ Over.mk f ↦
            ((Scheme.pointSmallEtale z.left).presheafFiber
              (A := ModuleCat.{u + 1} A)).obj F) z) := by
  obtain ⟨z', hz, rfl⟩ := Over.homMk_surjective z
  obtain ⟨w', hw, rfl⟩ := Over.homMk_surjective w
  change (Spec (.of Ω) ⟶ U) at z'
  change (Spec (.of Ω) ⟶ W.left) at w'
  change w' ≫ W.hom = z' at hw
  subst z'
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def forwardTransformation
    (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    F ⟶ (base f).op ⋙ (Scheme.pointSmallEtale x).skyscraperPresheaf
      (A := ModuleCat.{u + 1} A) (sum f A x F) where
  app W := Pi.lift (fun v ↦ forwardFamily f A x F W.unop v)
  naturality {W W'} g := by
    apply Pi.hom_ext
    intro v
    simp only [Category.assoc, Pi.lift_comp_π]
    change F.map g ≫ forwardFamily f A x F W'.unop v =
      (Pi.lift fun v ↦ forwardFamily f A x F W.unop v) ≫
        Pi.map' ((Scheme.pointSmallEtale x).fiber.map ((base f).map g.unop))
          (fun _ ↦ 𝟙 _) ≫ Pi.π _ v
    rw [Pi.map'_comp_π, ← Category.assoc, Pi.lift_comp_π, Category.comp_id]
    let z : Over.mk x ⟶ Over.mk f := v ≫ Over.homMk W'.unop.hom
    let w' : (Scheme.pointSmallEtale z.left).fiber.obj W'.unop := Over.homMk v.left
    let w := w' ≫ (Scheme.Etale.forget U).map g.unop
    have hv' : forgetPoint f x z W'.unop w' = v := by apply Over.OverMorphism.ext; rfl
    have hv : forgetPoint f x z W.unop w =
        (Scheme.pointSmallEtale x).fiber.map ((base f).map g.unop) v := by
      apply Over.OverMorphism.ext
      rfl
    rw [← hv, ← hv', forwardFamily_eq, forwardFamily_eq, ← Category.assoc]
    congr 1
    exact (Scheme.pointSmallEtale z.left).toPresheafFiber_w g.unop w' F

-- Descend the germ assignment first through the Kan extension and then through the stalk.
private noncomputable def forward (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    ((Scheme.pointSmallEtale x).presheafFiber (A := ModuleCat.{u + 1} A)).obj
      (presheaf f A F) ⟶ sum f A x F :=
  (Scheme.pointSmallEtale x).skyscraperPresheafHomEquiv.symm
    ((presheaf f A F).descOfIsLeftKanExtension ((base f).op.lanUnit.app F) _
      (forwardTransformation f A x F))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma forward_germ (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (W : U.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj ((base f).obj W)) :
    ((base f).op.lanUnit.app F).app (op W) ≫
        (Scheme.pointSmallEtale x).toPresheafFiber ((base f).obj W) v
          (presheaf f A F) ≫ forward f A x F = forwardFamily f A x F W v := by
  unfold forward
  rw [← GrothendieckTopology.Point.skyscraperPresheafHomEquiv_app_π,
    Equiv.apply_symm_apply, ← Category.assoc]
  have h := (presheaf f A F).descOfIsLeftKanExtension_fac_app
    ((base f).op.lanUnit.app F) _ (forwardTransformation f A x F) (op W)
  exact (congrArg (· ≫ Pi.π _ v) h).trans (Pi.lift_comp_π _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def backwardSummand
    (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) (z : Over.mk x ⟶ Over.mk f) :
    ((Scheme.pointSmallEtale z.left).presheafFiber (A := ModuleCat.{u + 1} A)).obj F ⟶
      ((Scheme.pointSmallEtale x).presheafFiber (A := ModuleCat.{u + 1} A)).obj
        (presheaf f A F) :=
  (Scheme.pointSmallEtale z.left).presheafFiberDesc
    (fun W w ↦ ((base f).op.lanUnit.app F).app (op W) ≫
      (Scheme.pointSmallEtale x).toPresheafFiber ((base f).obj W)
        (forgetPoint f x z W w) (presheaf f A F)) (by
    intro W W' g w
    rw [← Category.assoc, NatTrans.naturality, Category.assoc]
    congr 1
    exact (Scheme.pointSmallEtale x).toPresheafFiber_w
      ((base f).map g) (forgetPoint f x z W w) (presheaf f A F))

private lemma backwardSummand_germ (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (z : Over.mk x ⟶ Over.mk f) (W : U.Etale)
    (w : (Scheme.pointSmallEtale z.left).fiber.obj W) :
    (Scheme.pointSmallEtale z.left).toPresheafFiber W w F ≫ backwardSummand f A x F z =
      ((base f).op.lanUnit.app F).app (op W) ≫
        (Scheme.pointSmallEtale x).toPresheafFiber ((base f).obj W)
          (forgetPoint f x z W w) (presheaf f A F) := by
  exact (Scheme.pointSmallEtale z.left).toPresheafFiber_presheafFiberDesc _ _ _ _

open Classical in
private noncomputable def backward (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    sum f A x F ⟶
      ((Scheme.pointSmallEtale x).presheafFiber (A := ModuleCat.{u + 1} A)).obj
        (presheaf f A F) :=
  ModuleCat.ofHom (DirectSum.toModule A _ _
    (fun z ↦ (backwardSummand f A x F z).hom))

open Classical in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma backward_lof (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (z : Over.mk x ⟶ Over.mk f) :
    ModuleCat.ofHom (DirectSum.lof A _
      (fun z : Over.mk x ⟶ Over.mk f ↦
        ((Scheme.pointSmallEtale z.left).presheafFiber
          (A := ModuleCat.{u + 1} A)).obj F) z) ≫ backward f A x F =
      backwardSummand f A x F z := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  simp only [backward, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply]
  exact DirectSum.toModule_lof A
    (M := fun z : Over.mk x ⟶ Over.mk f ↦
      ((Scheme.pointSmallEtale z.left).presheafFiber
        (A := ModuleCat.{u + 1} A)).obj F)
    (φ := fun z ↦ (backwardSummand f A x F z).hom) z s

open Classical in
private lemma backward_forward (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    backward f A x F ≫ forward f A x F = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro z
  have hh : backwardSummand f A x F z ≫ forward f A x F =
      ModuleCat.ofHom (DirectSum.lof A _
        (fun z : Over.mk x ⟶ Over.mk f ↦
          ((Scheme.pointSmallEtale z.left).presheafFiber
            (A := ModuleCat.{u + 1} A)).obj F) z) := by
    apply (Scheme.pointSmallEtale z.left).presheafFiber_hom_ext
    intro W w
    rw [← Category.assoc, backwardSummand_germ, Category.assoc, forward_germ,
      forwardFamily_eq]
  have hcat := congrArg (fun h ↦ h ≫ forward f A x F) (backward_lof f A x F z)
  rw [Category.assoc, hh] at hcat
  exact congrArg ModuleCat.Hom.hom hcat

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma forward_backward (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    forward f A x F ≫ backward f A x F = 𝟙 _ := by
  apply hom_ext f A x F
  intro W v
  calc
    _ = (forwardFamily f A x F W v) ≫ backward f A x F := by
      simpa only [Category.assoc] using
        congrArg (· ≫ backward f A x F) (forward_germ f A x F W v)
    _ = _ := by
      dsimp only [forwardFamily]
      rw [Category.assoc, backward_lof]
      have hh := backwardSummand_germ f A x F
        (v ≫ Over.homMk W.hom) W (Over.homMk v.left)
      have hv : forgetPoint f x (v ≫ Over.homMk W.hom) W (Over.homMk v.left) = v := by
        apply Over.OverMorphism.ext
        rfl
      rw [hv] at hh
      exact hh.trans (by simp only [Category.comp_id])

private noncomputable def presheafIso (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    ((Scheme.pointSmallEtale x).presheafFiber (A := ModuleCat.{u + 1} A)).obj
      (presheaf f A F) ≅ sum f A x F where
  hom := forward f A x F
  inv := backward f A x F
  hom_inv_id := forward_backward f A x F
  inv_hom_id := backward_forward f A x F

open Classical in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma unit_naturality {F G : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A}
    (α : F ⟶ G) (W : U.Etale) :
    ((base f).op.lanUnit.app F).app (op W) ≫
        ((base f).op.lan.map α).app (op ((base f).obj W)) =
      α.app (op W) ≫ ((base f).op.lanUnit.app G).app (op W) := by
  exact (NatTrans.congr_app ((base f).op.lanUnit.naturality α) (op W)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def sheafIso
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj
      ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).obj F) ≅
        sum f A x F.obj :=
  (asIso ((Scheme.pointSmallEtale x).presheafFiber.map
    (toSheafify X.smallEtaleTopology (presheaf f A F.obj)))).symm ≪≫
      presheafIso f A x F.obj

end Etale.SumStalks

end AlgebraicGeometry
