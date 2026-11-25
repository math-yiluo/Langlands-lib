/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-!
# Fixed-ring module sheaves and modules over the constant ring sheaf

Source: Stacks Project, Modules on Sites, Tag 03CY, and its constant-ring specialization
on arbitrary covering-sieve topologies (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v)) [CommRing Λ]

set_option backward.isDefEq.respectTransparency false in
/-- Restrict scalars along the constant-ring sheafification unit, retaining the underlying
abelian presheaf. Source: Stacks Tag 03CY, constant-ring specialization
(auxiliary; not a blueprint node). -/
def constantRingModuleRestrictionPresheaf
    (M : ringedSiteModules.{max u v}
      ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ))) :
    Cᵒᵖ ⥤ ModuleCat.{max u v} Λ :=
  let P := (PresheafOfModules.restrictScalars
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj M.val
  { obj := P.obj
    map := fun f ↦ P.map f
    map_id := fun X ↦ by ext x; exact congrArg (fun f ↦ f x) (P.map_id X)
    map_comp := fun f g ↦ by
      ext x
      exact P.map_comp_apply f g x }

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along the unit, as a functor into fixed-ring module-valued sheaves.
The sheaf condition is reflected by forgetting module structure to abelian groups.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
def constantRingModuleRestriction :
    ringedSiteModules.{max u v}
      ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)) ⥤
        Sheaf J (ModuleCat.{max u v} Λ) where
  obj M := ⟨constantRingModuleRestrictionPresheaf J Λ M,
    Presheaf.isSheaf_of_isSheaf_comp J _
      (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v}) M.isSheaf⟩
  map f := { hom :=
    { app := fun X ↦ (ModuleCat.restrictScalars
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X).hom).map
          (f.val.app X)
      naturality := fun _ _ g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply f.val g x } }

/-- The two requirements on an action on the original sections: semilinear restrictions
and extension of the given fixed-ring action along the sheafification unit.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
def IsConstantRingModuleActionExtension (N : Sheaf J (ModuleCat.{max u v} Λ))
    (m : ∀ X : Cᵒᵖ,
      Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
        (N.obj.obj X)) : Prop :=
  (∀ (X Y : Cᵒᵖ) (f : X ⟶ Y)
    (s : ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
    (x : N.obj.obj X),
    N.obj.map f (@SMul.smul _ _ (m X).toSMul s x) =
      @SMul.smul _ _ (m Y).toSMul
        (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.map f s)
        (N.obj.map f x)) ∧
  (∀ (X : Cᵒᵖ) (a : Λ) (x : N.obj.obj X),
    @SMul.smul _ _ (m X).toSMul
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X a) x = a • x)

set_option backward.isDefEq.respectTransparency false in
/-- Regard a fixed-ring module sheaf as a module presheaf over the constant ring presheaf.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private def constantModulePresheaf (N : Sheaf J (ModuleCat.{max u v} Λ)) :
    PresheafOfModules.{max u v} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) :=
  { obj := N.obj.obj
    map := fun f ↦ N.obj.map f
    map_id := fun X ↦ by ext x; exact congrArg (fun f ↦ f x) (N.obj.map_id X)
    map_comp := fun f g ↦ by
      ext x
      exact congrArg (fun f ↦ f x) (N.obj.map_comp f g) }

set_option backward.isDefEq.respectTransparency false in
/-- Apply module sheafification to the identity of the underlying abelian sheaf.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private def constantModuleExtensionObj (N : Sheaf J (ModuleCat.{max u v} Λ)) :
    ringedSiteModules.{max u v}
      ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)) :=
  PresheafOfModules.sheafify
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))
    (M₀ := constantModulePresheaf J Λ N)
    (A := (sheafCompose J (forget₂ (ModuleCat Λ) AddCommGrpCat)).obj N) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified action is semilinear and extends the original scalar action.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private theorem constantModuleExtensionObj_property
    (N : Sheaf J (ModuleCat.{max u v} Λ)) :
    IsConstantRingModuleActionExtension J Λ N
      (fun X ↦ ((constantModuleExtensionObj J Λ N).val.obj X).isModule) := by
  constructor
  · intro X Y f s x
    exact (constantModuleExtensionObj J Λ N).val.map_smul f s x
  · intro X a x
    exact (((PresheafOfModules.toSheafify
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))
      (M₀ := constantModulePresheaf J Λ N)
      (A := (sheafCompose J (forget₂ (ModuleCat Λ) AddCommGrpCat)).obj N)
      (𝟙 _)).app X).hom.map_smul a x).symm

set_option backward.isDefEq.respectTransparency false in
/-- Bundle any compatible extended action on the original abelian sheaf.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private def constantActionObj (N : Sheaf J (ModuleCat.{max u v} Λ))
    (m : ∀ X : Cᵒᵖ,
      Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
        (N.obj.obj X)) (hm : IsConstantRingModuleActionExtension J Λ N m) :
    ringedSiteModules.{max u v}
      ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)) := by
  letI : ∀ X, Module
      (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
      ((N.obj ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat).obj X) := m
  exact ⟨PresheafOfModules.ofPresheaf
    (N.obj ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat) (fun {_ _} f s x ↦ hm.1 _ _ f s x),
    ((sheafCompose J (forget₂ (ModuleCat Λ) AddCommGrpCat)).obj N).property⟩

set_option backward.isDefEq.respectTransparency false in
/-- Local surjectivity of ring sheafification upgrades fixed-ring linearity to linearity.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private theorem constantAction_map_smul
    (N M : Sheaf J (ModuleCat.{max u v} Λ)) (f : N ⟶ M)
    (m : ∀ X : Cᵒᵖ,
      Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
        (N.obj.obj X))
    (n : ∀ X : Cᵒᵖ,
      Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
        (M.obj.obj X))
    (hm : IsConstantRingModuleActionExtension J Λ N m)
    (hn : IsConstantRingModuleActionExtension J Λ M n)
    (X : Cᵒᵖ)
    (s : ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
    (x : N.obj.obj X) :
    f.hom.app X (@SMul.smul _ _ (m X).toSMul s x) =
      @SMul.smul _ _ (n X).toSMul s (f.hom.app X x) := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  let P := constantActionObj J Λ N m hm
  let Q := constantActionObj J Λ M n hn
  let g : (PresheafOfModules.restrictScalars α).obj P.val ⟶
      (PresheafOfModules.restrictScalars α).obj Q.val :=
    PresheafOfModules.homMk
      (Functor.whiskerRight f.hom (forget₂ (ModuleCat Λ) AddCommGrpCat)) (by
        intro Y a y
        change f.hom.app Y (@SMul.smul _ _ (m Y).toSMul (α.app Y a) y) =
          @SMul.smul _ _ (n Y).toSMul (α.app Y a) (f.hom.app Y y)
        rw [hm.2, hn.2]
        exact (f.hom.app Y).hom.map_smul a y)
  let g' := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    α Q.isSheaf).symm g
  exact (g'.app X).hom.map_smul s x

set_option backward.isDefEq.respectTransparency false in
/-- The identity map is linear between any two extended actions, so they agree.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private theorem constantAction_unique
    (N : Sheaf J (ModuleCat.{max u v} Λ))
    (m n : ∀ X : Cᵒᵖ,
      Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
        (N.obj.obj X))
    (hm : IsConstantRingModuleActionExtension J Λ N m)
    (hn : IsConstantRingModuleActionExtension J Λ N n) : m = n := by
  funext X
  exact Module.ext' (m X) (n X)
    (fun s x ↦ constantAction_map_smul J Λ N N (𝟙 N) m n hm hn X s x)

set_option backward.isDefEq.respectTransparency false in
/-- Extend scalars on sections and retain the same underlying natural maps.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private def constantModuleExtension :
    Sheaf J (ModuleCat.{max u v} Λ) ⥤
      ringedSiteModules.{max u v}
        ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)) where
  obj := constantModuleExtensionObj J Λ
  map {N M} f := ⟨PresheafOfModules.homMk
    (Functor.whiskerRight f.hom (forget₂ (ModuleCat Λ) AddCommGrpCat))
    (constantAction_map_smul J Λ N M f _ _
      (constantModuleExtensionObj_property J Λ N)
      (constantModuleExtensionObj_property J Λ M))⟩
  map_id N := by ext X x; rfl
  map_comp f g := by ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Extension retains component maps and hence their addition.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private theorem constantModuleExtension_additive : (constantModuleExtension J Λ).Additive where
  map_add := by intros; ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction retains component maps and hence their addition.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private theorem constantModuleRestriction_additive :
    (constantRingModuleRestriction J Λ).Additive where
  map_add := by intros; ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity on sections identifies restriction after extension with the original sheaf.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private def constantModuleCounit :
    constantModuleExtension J Λ ⋙ constantRingModuleRestriction J Λ ≅ 𝟭 _ :=
  NatIso.ofComponents (fun N ↦
    { hom := { hom :=
        { app := fun X ↦ ModuleCat.ofHom
            (X := ((constantRingModuleRestriction J Λ).obj
              ((constantModuleExtension J Λ).obj N)).obj.obj X)
            (Y := N.obj.obj X)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun a x ↦ (constantModuleExtensionObj_property J Λ N).2 X a x }
          naturality := fun _ _ f ↦ by ext x; rfl } }
      inv := { hom :=
        { app := fun X ↦ ModuleCat.ofHom
            (X := N.obj.obj X)
            (Y := ((constantRingModuleRestriction J Λ).obj
              ((constantModuleExtension J Λ).obj N)).obj.obj X)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun a x ↦ ((constantModuleExtensionObj_property J Λ N).2 X a x).symm }
          naturality := fun _ _ f ↦ by ext x; rfl } }
      hom_inv_id := by ext X x; rfl
      inv_hom_id := by ext X x; rfl })
    (fun f ↦ by ext X x; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The original ring-sheaf action extends its own restriction of scalars.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private theorem constantModuleRestriction_property
    (M : ringedSiteModules.{max u v}
      ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ))) :
    IsConstantRingModuleActionExtension J Λ
      ((constantRingModuleRestriction J Λ).obj M)
      (fun X ↦ (M.val.obj X).isModule) := by
  constructor
  · intro X Y f s x
    exact M.val.map_smul f s x
  · intro X a x
    rfl

/-- Identity maps identify extension after restriction with the original module sheaf.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
private def constantModuleUnit :
    𝟭 _ ≅ constantRingModuleRestriction J Λ ⋙ constantModuleExtension J Λ :=
  NatIso.ofComponents (fun M ↦
    { hom := ⟨PresheafOfModules.homMk
        (𝟙 M.val.presheaf)
        (fun X s x ↦ constantAction_map_smul J Λ
          ((constantRingModuleRestriction J Λ).obj M)
          ((constantRingModuleRestriction J Λ).obj M) (𝟙 _)
          (fun X ↦ (M.val.obj X).isModule)
          (fun X ↦ ((constantModuleExtensionObj J Λ
            ((constantRingModuleRestriction J Λ).obj M)).val.obj X).isModule)
          (constantModuleRestriction_property J Λ M)
          (constantModuleExtensionObj_property J Λ _) X s x)⟩
      inv := ⟨PresheafOfModules.homMk (𝟙 M.val.presheaf)
        (fun X s x ↦ constantAction_map_smul J Λ
          ((constantRingModuleRestriction J Λ).obj M)
          ((constantRingModuleRestriction J Λ).obj M) (𝟙 _)
          (fun X ↦ ((constantModuleExtensionObj J Λ
            ((constantRingModuleRestriction J Λ).obj M)).val.obj X).isModule)
          (fun X ↦ (M.val.obj X).isModule)
          (constantModuleExtensionObj_property J Λ _)
          (constantModuleRestriction_property J Λ M) X s x)⟩
      hom_inv_id := by ext X x; rfl
      inv_hom_id := by ext X x; rfl })
    (fun f ↦ by ext X x; rfl)

/-- Restriction of scalars gives an additive equivalence. The inverse retains the abelian
sheaf and its maps. There is a unique extended action on the original sections, and every
fixed-ring linear natural map is linear for any such extended actions.

Source: Stacks Tag 03CY, constant-ring extension to arbitrary sieve sites
(auxiliary; not a blueprint node).

Proof:
1. Fixed-ring module presheaves are modules over the constant ring presheaf. Matching tuples
form modules componentwise, so forgetting to abelian groups preserves and reflects the
covering-sieve limit condition.
2. Use Mathlib's module-sheafification construction from
lem-cbc-sieve-module-sheafification with the identity map of the underlying abelian sheaf.
This equips the original sections with a genuine module action over the sheafified ring.
3. The construction supplies semilinear restrictions and its unit is fixed-ring linear.
Since the abelian unit here is the identity, this proves extension of the original action.
4. Fullness of scalar restriction lifts the identity between any two extensions. Its underlying
identity map is linear, which makes the two scalar actions equal.
5. Fullness likewise lifts every fixed-ring linear natural map, retaining its components and
proving linearity for the extended actions.
6. Restriction after extension is the original action. Uniqueness identifies extension after
restriction with the original sheaf-of-modules action. Identity underlying maps give both
natural inverse isomorphisms. Both functors preserve addition because their maps are unchanged.
No nonempty-site, nonzero-ring, fibre-product or subcanonicity hypothesis is used. -/
theorem constant_ring_module_sheaves :
    (∃ e : ringedSiteModules.{max u v}
        ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)) ≌
          Sheaf J (ModuleCat.{max u v} Λ),
      e.functor = constantRingModuleRestriction J Λ ∧
      e.functor.Additive ∧ e.inverse.Additive ∧
      e.inverse ⋙ SheafOfModules.toSheaf _ =
        sheafCompose J (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v})) ∧
    (∀ N : Sheaf J (ModuleCat.{max u v} Λ),
      ∃! m : ∀ X : Cᵒᵖ,
        Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
          (N.obj.obj X), IsConstantRingModuleActionExtension J Λ N m) ∧
    (∀ (N M : Sheaf J (ModuleCat.{max u v} Λ)) (f : N ⟶ M)
      (m : ∀ X : Cᵒᵖ,
        Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
          (N.obj.obj X))
      (n : ∀ X : Cᵒᵖ,
        Module (((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
          (M.obj.obj X)),
      IsConstantRingModuleActionExtension J Λ N m →
      IsConstantRingModuleActionExtension J Λ M n →
      ∀ (X : Cᵒᵖ)
        (s : ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)).obj.obj X)
        (x : N.obj.obj X),
        f.hom.app X (@SMul.smul _ _ (m X).toSMul s x) =
          @SMul.smul _ _ (n X).toSMul s (f.hom.app X x)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Equivalence.mk (constantRingModuleRestriction J Λ) (constantModuleExtension J Λ)
      (constantModuleUnit J Λ) (constantModuleCounit J Λ), rfl,
      constantModuleRestriction_additive J Λ, constantModuleExtension_additive J Λ, ?_⟩
    rfl
  · intro N
    refine ⟨_, constantModuleExtensionObj_property J Λ N, ?_⟩
    intro m hm
    exact constantAction_unique J Λ N m _ hm (constantModuleExtensionObj_property J Λ N)
  · exact constantAction_map_smul J Λ

end CategoryTheory
