/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Grothendieck module sheaves with independent site and coefficient universes

Source: Stacks Project, Modules on Sites, Tags 03CV and 03DA; Cohomology on Sites,
Section 07A5; Injectives, Tag 079Q (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe c h r s

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

section

variable {C : Type c} [Category.{h} C] (R : Cᵒᵖ ⥤ RingCat.{r})

set_option backward.isDefEq.respectTransparency false in
private noncomputable def freeObj (A : C) : PresheafOfModules.{max c h r s} R where
  obj X := ModuleCat.of (R.obj X) (ULift.{max c h r s} (unop X ⟶ A) →₀ R.obj X)
  map {X Y} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of (R.obj Y) (ULift.{max c h r s} (unop Y ⟶ A) →₀ R.obj Y)))
    (Finsupp.linearCombination (R.obj X)
      (M := (ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj Y) (ULift.{max c h r s} (unop Y ⟶ A) →₀ R.obj Y)))
      (fun a ↦ Finsupp.single (ULift.up (f.unop ≫ a.down)) 1))
  map_id X := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    simp [Finsupp.linearCombination_single]
    rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    simp [Finsupp.linearCombination_single, Category.assoc]

@[simp]
private lemma freeObj_map_single (A : C) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : ULift.{max c h r s} (unop X ⟶ A)) (b : R.obj X) :
    (freeObj.{c, h, r, s} R A).map f (Finsupp.single a b) =
      Finsupp.single (ULift.up (f.unop ≫ a.down)) (R.map f b) := by
  change (Finsupp.linearCombination (R.obj X)
    (M := (ModuleCat.restrictScalars (R.map f).hom).obj ((freeObj R A).obj Y))
    (fun a ↦ Finsupp.single (ULift.up (f.unop ≫ a.down)) 1)) (Finsupp.single a b) = _
  rw [Finsupp.linearCombination_single]
  change (R.map f b) • (Finsupp.single _ 1 : _ →₀ R.obj Y) = _
  simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def freeDesc (A : C) (M : PresheafOfModules.{max c h r s} R)
    (s : M.obj (op A)) : freeObj R A ⟶ M where
  app X := ModuleCat.ofHom
    (Finsupp.linearCombination (R.obj X)
      (fun a : ULift.{max c h r s} (unop X ⟶ A) ↦ M.map a.down.op s))
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    change (Finsupp.linearCombination (R.obj Y)
      (fun a : ULift.{max c h r s} (unop Y ⟶ A) ↦ M.map a.down.op s))
      ((freeObj R A).map f (Finsupp.single a 1)) =
      M.map f ((Finsupp.linearCombination (R.obj X)
      (fun a : ULift.{max c h r s} (unop X ⟶ A) ↦ M.map a.down.op s))
        (Finsupp.single a 1))
    simp only [freeObj_map_single, map_one, Finsupp.linearCombination_single, one_smul]
    rw [op_comp, M.map_comp_apply, Quiver.Hom.op_unop]

@[simp]
private lemma freeDesc_single (A : C) (M : PresheafOfModules.{max c h r s} R)
    (s : M.obj (op A)) (X : Cᵒᵖ)
    (a : ULift.{max c h r s} (unop X ⟶ A)) (b : R.obj X) :
    (freeDesc R A M s).app X (Finsupp.single a b) = b • M.map a.down.op s :=
  Finsupp.linearCombination_single _ _ _

end

/-- Module sheaves form a Grothendieck abelian category in a common universe containing
both the small site and its ring coefficients. The rings need not be commutative.
Source: Stacks Project, Modules on Sites, Tags 03CV and 03DA; Cohomology on Sites,
Section 07A5; Injectives, Tag 079Q (auxiliary; not a blueprint node).

Proof:
1. Construct free representable presheaves in the common module universe as finitely
supported functions on the lifted hom sets, with coefficients in the original rings.
Restrictions precompose the basis labels and apply the ring restriction to coefficients.
A section x over X defines a map out of this free presheaf by sending the basis label
f : Y ⟶ X to the restriction of x along f; its value at the identity basis vector is x.
2. Sheafify these free presheaves. If two maps agree after every map from each such
sheaf, adjunction makes their underlying maps agree on all free presheaf maps.
Evaluation at the identity basis vector gives equality on every section, hence equality
of the original maps. Their coproduct is therefore a separator.
3. Module-sheaf colimits exist by sheafifying presheaf colimits. The underlying abelian
sheaf functor preserves colimits and finite limits and reflects isomorphisms. Since
filtered colimits of abelian sheaves are exact, they are exact for module sheaves too.
The separator and these properties give the stated Grothendieck abelian structure. -/
theorem isGrothendieckAbelianOfUniverses
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{r}) :
    IsGrothendieckAbelian.{max c h r s}
      (ringedSiteModules.{max c h r s} R) := by
  have : HasFilteredColimitsOfSize.{max c h r s, max c h r s}
      (SheafOfModules.{max c h r s} R) := ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{max c h r s, max c h r s}
      (SheafOfModules.{max c h r s} R) :=
    ⟨fun K _ _ ↦ HasExactColimitsOfShape.domain_of_functor K
      (toSheaf.{max c h r s} R)⟩
  have hsep : ObjectProperty.IsSeparating (.ofObj fun X : C ↦
      (PresheafOfModules.sheafification.{max c h r s} (𝟙 R.obj)).obj
        (freeObj.{c, h, r, s} R.obj X)) := by
    let adj := PresheafOfModules.sheafificationAdjunction.{max c h r s} (𝟙 R.obj)
    intro M N f g hfg
    apply (SheafOfModules.forget.{max c h r s} R ⋙
      PresheafOfModules.restrictScalars.{max c h r s}
      (𝟙 R.obj)).map_injective
    ext ⟨X⟩ x
    let a := freeDesc.{c, h, r, s} R.obj X
      ((PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M.val) x
    have heq := hfg _ (ObjectProperty.ofObj_apply _ X) ((adj.homEquiv _ _).symm a)
    have hh := congrArg (adj.homEquiv _ _) heq
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] at hh
    have hv := congrArg (fun k ↦ k.app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1)) hh
    have ha : a.app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1) = x := by
      dsimp only [a]
      rw [freeDesc_single]
      simp
    change f.val.app (op X) (a.app (op X) _) =
      g.val.app (op X) (a.app (op X) _) at hv
    rw [ha] at hv
    exact hv
  have : HasSeparator (SheafOfModules.{max c h r s} R) :=
    ⟨_, hsep.isSeparator_coproduct⟩
  exact {}

end SheafOfModules
