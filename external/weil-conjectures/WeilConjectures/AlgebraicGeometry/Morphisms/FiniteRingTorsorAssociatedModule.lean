/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule

/-!
# The associated module sheaf with general commutative coefficients

The existing prime-coefficient construction stays unchanged. This variant uses the
same equivariant locally constant formulas directly over the specified coefficient ring.

## References

* Stacks Project, Tags 0DV5 (3), 0DV6, 04TR and 04TS
* Stacks Project, Tags 0DV5 (3), 04TR and 04TS
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u r
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

variable {V : Scheme.{u}} {P : Type u} [Group P] [Finite P]
  (c : Scheme.GaloisCover (ULift.{u + 1} P) V)

section GenericRing

variable (R : Type r) [CommRing R]

/-- Locally constant equivariant sections form a submodule. -/
def equivariantSectionsOver (N : Rep.{u + 1} R P) (W : V.Etale) :
    Submodule R (LocallyConstant (c.sectionSpace W) N.V) where
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
noncomputable def equivariantRestrictionOver (N : Rep.{u + 1} R P)
    {W W' : V.Etale} (f : W ⟶ W') :
    c.equivariantSectionsOver R N W' →ₗ[R] c.equivariantSectionsOver R N W where
  toFun s := ⟨LocallyConstant.comap ⟨c.sectionRestriction f,
    (c.sectionRestriction f).continuous⟩ s.val, by
      intro g x
      change s.val (c.sectionRestriction f (c.sectionAction W g x)) =
        N.ρ g (s.val (c.sectionRestriction f x))
      have haction : c.sectionAction W g ≫ c.sectionRestriction f =
          c.sectionRestriction f ≫ c.sectionAction W' g := by
        apply pullback.hom_ext <;> simp [sectionAction, sectionRestriction]
      rw [← Scheme.Hom.comp_apply, haction,
        Scheme.Hom.comp_apply]
      exact s.property g _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The presheaf of equivariant locally constant module sections. -/
noncomputable def equivariantModulePresheafOver (N : Rep.{u + 1} R P) :
    V.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R where
  obj W := ModuleCat.of _ (c.equivariantSectionsOver R N W.unop)
  map f := ModuleCat.ofHom (c.equivariantRestrictionOver R N f.unop)
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
noncomputable def equivariantModuleMapOver {N N' : Rep.{u + 1} R P} (f : N ⟶ N') :
    c.equivariantModulePresheafOver R N ⟶ c.equivariantModulePresheafOver R N' where
  app W := ModuleCat.ofHom
    { toFun := fun s ↦ ⟨LocallyConstant.map f.hom s.val, by
        intro g x
        change f.hom (s.val (c.sectionAction W.unop g x)) = N'.ρ g (f.hom (s.val x))
        rw [s.property, Rep.hom_comm_apply]⟩
      map_add' := by intro a b; ext x; exact map_add f.hom _ _
      map_smul' := by intro r a; ext x; exact map_smul f.hom _ _ }
  naturality _ _ f := by ext s; rfl

/-- The functor of equivariant section presheaves. -/
noncomputable def equivariantModulePresheafFunctorOver :
    Rep.{u + 1} R P ⥤ (V.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R) where
  obj := c.equivariantModulePresheafOver R
  map := c.equivariantModuleMapOver R
  map_id N := by ext W s; rfl
  map_comp f g := by ext W s; rfl

instance equivariantModulePresheafFunctorOver_additive :
    (c.equivariantModulePresheafFunctorOver R).Additive where
  map_add {N N' f g} := by
    ext W s
    rfl

end GenericRing

section LargeRing

variable (R : Type (u + 1)) [CommRing R]

/-- The associated sheaf functor for an arbitrary commutative coefficient ring. -/
noncomputable def associatedModuleFunctorOver :
    Rep.{u + 1} R P ⥤ Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  c.equivariantModulePresheafFunctorOver R ⋙ presheafToSheaf V.smallEtaleTopology _

instance associatedModuleFunctorOver_additive : (c.associatedModuleFunctorOver R).Additive := by
  let _ : (presheafToSheaf V.smallEtaleTopology (ModuleCat.{u + 1} R)).Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold associatedModuleFunctorOver
  infer_instance

end LargeRing

end AlgebraicGeometry.Scheme.GaloisCover
