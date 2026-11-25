/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
public import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-!
# Canonical sections of the lifted étale structure-module sheaf

Source: Stacks Tags 0096, 01CA, 03DR, 03DU; the restriction-identification step of
blueprint `lem-sc-as-sequence-construction-helper`.
-/

@[expose] public section
universe u v w
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackObj Scheme.Modules.tensorPullbackObjUnitToUnit

/-- Evaluate the adjoint structure-module isomorphism on the top open.
Source: Stacks Tags 0096 and 01CA
(blueprint: lem-sc-as-sequence-construction-helper-restriction). -/
noncomputable def tensorStructureSectionsEquiv {A B : Scheme.{u}} (f : A ⟶ B) :
    Γ((Scheme.Modules.tensorPullback f).obj (SheafOfModules.unit B.ringCatSheaf), ⊤) ≃+
      Γ(A, ⊤) := by
  have : IsIso (Scheme.Modules.tensorPullbackObjUnitToUnit f) :=
    (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso f).1
  exact AddEquiv.ofBijective
    ((Scheme.Modules.tensorPullbackObjUnitToUnit f).app ⊤).hom
    (ConcreteCategory.bijective_of_isIso
      ((Scheme.Modules.tensorPullbackObjUnitToUnit f).app ⊤))

/-- Remove the universe lift and identify pullback sections with regular functions.
Source: Stacks Tags 0096, 01CA, 03DR, 03DU
(blueprint: lem-sc-as-sequence-construction-helper-restriction). -/
noncomputable def etaleStructureSectionsEquiv (C : Scheme.{u}) (U : C.Etaleᵒᵖ) :
    ((sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C))).obj.obj U ≃+
        Γ(U.unop.left, ⊤) :=
  AddEquiv.ulift.trans (tensorStructureSectionsEquiv U.unop.hom)

private theorem tensorStructureSectionsEquiv_apply {A B : Scheme.{u}}
    (f : A ⟶ B)
    (x : Γ((Scheme.Modules.tensorPullback f).obj (SheafOfModules.unit B.ringCatSheaf), ⊤)) :
    tensorStructureSectionsEquiv f x = (Scheme.Modules.tensorPullbackObjUnitToUnit f).app ⊤ x :=
  rfl

attribute [local irreducible] tensorStructureSectionsEquiv etaleStructureSectionsEquiv

private theorem tensorStructureSectionsEquiv_toHom {A B : Scheme.{u}} (f : A ⟶ B) :
    AddCommGrpCat.ofHom (tensorStructureSectionsEquiv f).toAddMonoidHom =
      (Scheme.Modules.tensorPullbackObjUnitToUnit f).app ⊤ := by
  ext y
  exact tensorStructureSectionsEquiv_apply f y

private theorem liftedSheafMap_apply {D : Type v} [Category.{w} D]
    (J : GrothendieckTopology D) (F : Sheaf J AddCommGrpCat.{u})
    {U V : Dᵒᵖ} (g : U ⟶ V) {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (a : F.obj.obj U ≃+ M) (b : F.obj.obj V ≃+ N) (r : M →+ N)
    (h : F.obj.map g ≫ AddCommGrpCat.ofHom b.toAddMonoidHom =
      AddCommGrpCat.ofHom a.toAddMonoidHom ≫ AddCommGrpCat.ofHom r)
    (x : ((sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F).obj.obj U) :
    (AddEquiv.ulift.trans b)
        (((sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F).obj.map g x) =
      r ((AddEquiv.ulift.trans a) x) :=
  ConcreteCategory.congr_hom h x.down

private theorem tensorStructureMap_comp {A B D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) :
    (Scheme.Modules.tensorSectionsComp a b).hom.app (SheafOfModules.unit D.ringCatSheaf) ≫
        Scheme.Modules.tensorPullbackObjUnitToUnit (a ≫ b) =
      (Scheme.Modules.tensorPullback a).map (Scheme.Modules.tensorPullbackObjUnitToUnit b) ≫
        Scheme.Modules.tensorPullbackObjUnitToUnit a := by
  let adjA := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction a)
  let adjB := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction b)
  let adjAB := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (a ≫ b))
  apply ((adjB.comp adjA).homEquiv _ _).injective
  have hu := unit_conjugateEquiv_symm adjAB (adjB.comp adjA)
    (Scheme.Modules.pushforwardComp a b).inv (SheafOfModules.unit D.ringCatSheaf)
  have ha := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso a).2
  have hb := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso b).2
  have hab := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso (a ≫ b)).2
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [Functor.map_comp, ← Category.assoc]
  change adjAB.unit.app _ ≫ (Scheme.Modules.pushforwardComp a b).inv.app _ =
    (adjB.comp adjA).unit.app _ ≫ (Scheme.Modules.pushforward a ⋙
      Scheme.Modules.pushforward b).map ((Scheme.Modules.tensorSectionsComp a b).hom.app _)
    at hu
  rw [← hu, Category.assoc]
  rw [← (Scheme.Modules.pushforwardComp a b).inv.naturality]
  rw [← Category.assoc, hab]
  rw [Adjunction.comp_unit_app, Category.assoc]
  dsimp only [Functor.comp_map]
  have hn : adjA.unit.app _ ≫ (Scheme.Modules.pushforward a).map
      ((Scheme.Modules.tensorPullback a).map (Scheme.Modules.tensorPullbackObjUnitToUnit b) ≫
        Scheme.Modules.tensorPullbackObjUnitToUnit a) =
      Scheme.Modules.tensorPullbackObjUnitToUnit b ≫
        SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom := by
    rw [Functor.map_comp, ← Category.assoc]
    erw [adjA.unit_naturality (Scheme.Modules.tensorPullbackObjUnitToUnit b)]
    rw [Category.assoc, ha]
  rw [← Functor.map_comp, hn, Functor.map_comp, ← Category.assoc, hb]
  ext W x
  rfl

private theorem tensorStructureMap_sections {A B : Scheme.{u}} (a : A ⟶ B)
    (G : B.Modules) (φ : G ⟶ SheafOfModules.unit B.ringCatSheaf) :
    Scheme.Modules.tensorSectionsUnit a G ≫
        ((Scheme.Modules.tensorPullback a).map φ).app ⊤ ≫
          (Scheme.Modules.tensorPullbackObjUnitToUnit a).app ⊤ =
      φ.app ⊤ ≫ AddCommGrpCat.ofHom a.appTop.hom.toAddMonoidHom := by
  let adjA := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction a)
  have hn := congrArg (fun ψ ↦ ψ.app ⊤) (adjA.unit_naturality φ)
  change (adjA.unit.app G).app ⊤ ≫ ((Scheme.Modules.tensorPullback a).map φ).app ⊤ =
    φ.app ⊤ ≫ (adjA.unit.app (SheafOfModules.unit B.ringCatSheaf)).app ⊤ at hn
  have he := congrArg (fun ψ ↦ ψ.app ⊤)
    (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso a).2
  change (adjA.unit.app (SheafOfModules.unit B.ringCatSheaf)).app ⊤ ≫
    (Scheme.Modules.tensorPullbackObjUnitToUnit a).app ⊤ =
      AddCommGrpCat.ofHom a.appTop.hom.toAddMonoidHom at he
  have hi : homOfLE a.preimage_top.ge =
      𝟙 (⊤ : TopologicalSpace.Opens A) := rfl
  unfold Scheme.Modules.tensorSectionsUnit
  erw [hi, op_id, ((Scheme.Modules.tensorPullback a).obj G).presheaf.map_id,
    Category.comp_id, ← Category.assoc, hn, Category.assoc, he]

private theorem tensorStructureMap_restriction {A B D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ D) (h : a ≫ b = c) :
    (Scheme.Modules.tensorSectionsUnit a
          ((Scheme.Modules.tensorPullback b).obj (SheafOfModules.unit D.ringCatSheaf)) ≫
        ((Scheme.Modules.tensorSectionsComp a b).hom.app
          (SheafOfModules.unit D.ringCatSheaf)).app ⊤ ≫
        (eqToHom (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj
          (SheafOfModules.unit D.ringCatSheaf)) h)).app ⊤) ≫
        (Scheme.Modules.tensorPullbackObjUnitToUnit c).app ⊤ =
      (Scheme.Modules.tensorPullbackObjUnitToUnit b).app ⊤ ≫
        AddCommGrpCat.ofHom a.appTop.hom.toAddMonoidHom := by
  subst c
  simp only [eqToHom_refl, Scheme.Modules.Hom.id_app, Category.comp_id]
  rw [Category.assoc, ← Scheme.Modules.Hom.comp_app, tensorStructureMap_comp,
    Scheme.Modules.Hom.comp_app]
  exact tensorStructureMap_sections a _ (Scheme.Modules.tensorPullbackObjUnitToUnit b)

private theorem tensorStructureMap_sections_hom {A B D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ D)
    (r : Γ((Scheme.Modules.tensorPullback b).obj (SheafOfModules.unit D.ringCatSheaf), ⊤) ⟶
      Γ((Scheme.Modules.tensorPullback c).obj (SheafOfModules.unit D.ringCatSheaf), ⊤))
    (hr : r ≫ (Scheme.Modules.tensorPullbackObjUnitToUnit c).app ⊤ =
      (Scheme.Modules.tensorPullbackObjUnitToUnit b).app ⊤ ≫
        AddCommGrpCat.ofHom a.appTop.hom.toAddMonoidHom) :
    r ≫ AddCommGrpCat.ofHom (tensorStructureSectionsEquiv c).toAddMonoidHom =
      AddCommGrpCat.ofHom (tensorStructureSectionsEquiv b).toAddMonoidHom ≫
        AddCommGrpCat.ofHom a.appTop.hom.toAddMonoidHom := by
  rw [tensorStructureSectionsEquiv_toHom, tensorStructureSectionsEquiv_toHom]
  exact hr

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The canonical section identifications commute with étale restrictions.
Source: blueprint `lem-sc-as-sequence-construction-helper`, proof step 3;
Stacks Tags 0096 and 01CA (adjoint structure map), 03DR equation (35.8.1),
and 03DU item 4 (the étale sections presheaf).
(blueprint: lem-sc-as-sequence-construction-helper-restriction)

Proof: Write epsilon_u for the adjoint structure-module map. The normalized
composition isomorphism c_{g,u} is the conjugate of the pushforward composition
identification. Its unit equation and the defining adjunction equation of epsilon
show that c_{g,u} followed by epsilon_{g >> u} equals g^*(epsilon_u) followed by
epsilon_g: apply the composite adjunction Hom bijection; use unit naturality and
then the two equations eta_u >> u_*(epsilon_u) = u-sharp and
eta_g >> g_*(epsilon_g) = g-sharp. The resulting composite structure map is
(g >> u)-sharp, so injectivity of the Hom bijection proves equality. Transport
along the site relation g >> u = v preserves epsilon by equality elimination.
Evaluate at the top open, where inverse image of top is top and the induced
restriction is the identity. Naturality of eta_g moves epsilon_u past section
pullback. The equation for epsilon_g then identifies the remaining composite
with g-sharp. Finally, ULift.down commutes with the lifted map, giving the
stated identity. This also covers the empty scheme, identities and composites;
no nonemptiness or characteristic assumption is used. -/
theorem etaleStructureSectionsEquiv_naturality (C : Scheme.{u})
    (U V : C.Etaleᵒᵖ) (g : U ⟶ V)
    (x : ((sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C))).obj.obj U) :
    etaleStructureSectionsEquiv C V
      (((sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C))).obj.map g x) =
      g.unop.left.appTop (etaleStructureSectionsEquiv C U x) := by
  have hm : Scheme.Modules.etaleTensorSectionsRestriction (Scheme.Modules.unitObj C) g.unop ≫
        (Scheme.Modules.tensorPullbackObjUnitToUnit V.unop.hom).app ⊤ =
      (Scheme.Modules.tensorPullbackObjUnitToUnit U.unop.hom).app ⊤ ≫
        AddCommGrpCat.ofHom g.unop.left.appTop.hom.toAddMonoidHom := by
    exact tensorStructureMap_restriction (D := C)
      g.unop.left U.unop.hom V.unop.hom g.unop.w
  unfold etaleStructureSectionsEquiv
  apply liftedSheafMap_apply C.smallEtaleTopology
    (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C)) g
    (tensorStructureSectionsEquiv U.unop.hom) (tensorStructureSectionsEquiv V.unop.hom)
    g.unop.left.appTop.hom.toAddMonoidHom
  exact tensorStructureMap_sections_hom (D := C) g.unop.left U.unop.hom V.unop.hom
    (Scheme.Modules.etaleTensorSectionsRestriction (Scheme.Modules.unitObj C) g.unop) hm

end AlgebraicGeometry
