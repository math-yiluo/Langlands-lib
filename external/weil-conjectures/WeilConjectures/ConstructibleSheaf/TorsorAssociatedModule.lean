/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Equivariant sections on a finite torsor

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lemma-reduction-unipotent-local-system--1)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

variable {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
  (c : Scheme.GaloisCover (ULift.{u + 1} P) V)

/-- The total space of the torsor above an etale object. -/
noncomputable abbrev sectionSpace (W : V.Etale) : Scheme.{u} := pullback W.hom c.π

/-- The action on the total space above an etale object. -/
noncomputable def sectionAction (W : V.Etale) (g : P) :
    c.sectionSpace W ⟶ c.sectionSpace W :=
  pullback.map W.hom c.π W.hom c.π (𝟙 _) (c.smul ⟨g⟩) (𝟙 _)
    (by simp) (by simp [c.smul_π])

/-- The map of total spaces induced by a map of etale objects. -/
noncomputable def sectionRestriction {W W' : V.Etale} (f : W ⟶ W') :
    c.sectionSpace W ⟶ c.sectionSpace W' :=
  pullback.map W.hom c.π W'.hom c.π f.left (𝟙 _) (𝟙 _)
    (by simp [MorphismProperty.Over.w f]) (by simp)

private theorem sectionRestriction_action {W W' : V.Etale} (f : W ⟶ W') (g : P) :
    c.sectionAction W g ≫ c.sectionRestriction f =
      c.sectionRestriction f ≫ c.sectionAction W' g := by
  apply pullback.hom_ext <;> simp [sectionAction, sectionRestriction]

/-- Locally constant equivariant sections form a submodule. -/
def equivariantSections (N : Rep.{u + 1} (ZMod ℓ) P) (W : V.Etale) :
    Submodule (ZMod ℓ) (LocallyConstant (c.sectionSpace W) N.V) where
  carrier := {s | ∀ (g : P) (x : c.sectionSpace W), s (c.sectionAction W g x) = N.ρ g (s x)}
  zero_mem' := by intro g x; simp
  add_mem' := by
    intro a b ha hb g x
    change a _ + b _ = N.ρ g (a x + b x)
    rw [ha, hb, map_add]
  smul_mem' := by
    intro r a ha g x
    change r • a _ = N.ρ g (r • a x)
    rw [ha, map_smul]

/-- Restriction of equivariant sections. -/
noncomputable def equivariantRestriction (N : Rep.{u + 1} (ZMod ℓ) P)
    {W W' : V.Etale} (f : W ⟶ W') :
    c.equivariantSections ℓ N W' →ₗ[ZMod ℓ] c.equivariantSections ℓ N W where
  toFun s := ⟨LocallyConstant.comap ⟨c.sectionRestriction f,
    (c.sectionRestriction f).continuous⟩ s.val, by
      intro g x
      change s.val (c.sectionRestriction f (c.sectionAction W g x)) =
        N.ρ g (s.val (c.sectionRestriction f x))
      rw [← Scheme.Hom.comp_apply, sectionRestriction_action,
        Scheme.Hom.comp_apply]
      exact s.property g _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The presheaf of equivariant locally constant module sections. -/
noncomputable def equivariantModulePresheaf (N : Rep.{u + 1} (ZMod ℓ) P) :
    V.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod ℓ) where
  obj W := ModuleCat.of _ (c.equivariantSections ℓ N W.unop)
  map f := ModuleCat.ofHom (c.equivariantRestriction ℓ N f.unop)
  map_id W := by
    ext s x
    change s.val (c.sectionRestriction (𝟙 W.unop) x) = s.val x
    have h : c.sectionRestriction (𝟙 W.unop) = 𝟙 (c.sectionSpace W.unop) := by
      change pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _
      exact pullback.map_id
    rw [h]
    rfl
  map_comp f g := by
    ext s x
    change s.val (c.sectionRestriction (g.unop ≫ f.unop) x) =
      s.val (c.sectionRestriction f.unop (c.sectionRestriction g.unop x))
    have h : c.sectionRestriction (g.unop ≫ f.unop) =
        c.sectionRestriction g.unop ≫ c.sectionRestriction f.unop := by
      apply pullback.hom_ext
      · simp only [sectionRestriction, pullback.map, pullback.lift_fst_assoc,
          pullback.lift_fst, Category.assoc]
        rfl
      · simp [sectionRestriction]
    rw [h, Scheme.Hom.comp_apply]

/-- An intertwiner acts pointwise on equivariant sections. -/
noncomputable def equivariantModuleMap {N N' : Rep.{u + 1} (ZMod ℓ) P} (f : N ⟶ N') :
    c.equivariantModulePresheaf ℓ N ⟶ c.equivariantModulePresheaf ℓ N' where
  app W := ModuleCat.ofHom
    { toFun := fun s ↦ ⟨LocallyConstant.map f.hom s.val, by
        intro g x
        change f.hom (s.val (c.sectionAction W.unop g x)) = N'.ρ g (f.hom (s.val x))
        rw [s.property, Rep.hom_comm_apply]⟩
      map_add' := by intro a b; ext x; exact map_add f.hom _ _
      map_smul' := by intro r a; ext x; exact map_smul f.hom _ _ }
  naturality _ _ f := by ext s; rfl

/-- The functor of equivariant section presheaves. -/
noncomputable def equivariantModulePresheafFunctor :
    Rep.{u + 1} (ZMod ℓ) P ⥤ (V.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod ℓ)) where
  obj := c.equivariantModulePresheaf ℓ
  map := c.equivariantModuleMap ℓ
  map_id N := by ext W s; rfl
  map_comp f g := by ext W s; rfl

instance equivariantModulePresheafFunctor_additive :
    (c.equivariantModulePresheafFunctor ℓ).Additive where
  map_add {N N' f g} := by
    ext W s
    rfl

/-- The associated module sheaf is the sheafification of equivariant locally constant
sections on the total space of the torsor above each etale object. Scalars are restricted
along the ring equivalence from the lifted coefficient ring to the coefficient ring.
Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lemma-reduction-unipotent-local-system--1) -/
noncomputable def associatedModuleFunctor :
    Rep.{u + 1} (ZMod ℓ) P ⥤
      Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) :=
  c.equivariantModulePresheafFunctor ℓ ⋙
    (Functor.whiskeringRight V.Etaleᵒᵖ _ _).obj
      (ModuleCat.restrictScalars.{u + 1}
        (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)) ⋙
    presheafToSheaf V.smallEtaleTopology _

instance associatedModuleFunctor_additive : (c.associatedModuleFunctor ℓ).Additive := by
  let _ : (presheafToSheaf V.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold associatedModuleFunctor
  infer_instance

end AlgebraicGeometry.Scheme.GaloisCover
