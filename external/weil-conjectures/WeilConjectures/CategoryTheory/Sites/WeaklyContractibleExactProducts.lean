/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleProducts

/-!
# Exact products of sheaves of modules on sites with enough weakly contractible objects

If every object of a site is covered by weakly contractible objects, products of sheaves of
modules are exact (Bhatt–Scholze, Proposition 3.1.10; Stacks 0947): epimorphisms of sheaves are
detected by surjectivity on sections over weakly contractible objects, sections commute with
products, and products of surjections of modules are surjective.

## Main results

- `CategoryTheory.GrothendieckTopology.hasExactLimitsOfShape_discrete_of_forall_exists`:
  products of sheaves of modules are exact.
-/

@[expose] public section

universe w w' v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type w} [Ring R]
  [HasSheafify J (ModuleCat.{w} R)] [J.WEqualsLocallyBijective (ModuleCat.{w} R)]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))] (P : C → Prop)
  (hP : ∀ V : C, ∃ (ι : Type w') (W : ι → C) (f : ∀ i, W i ⟶ V),
    (∀ i, P (W i)) ∧ Sieve.ofArrows W f ∈ J V)
  (hPW : ∀ W, P W → J.IsWeaklyContractible.{w} W)

include hP hPW in
/-- **Stacks 0947 (2).** If every object of the site is covered by weakly contractible objects,
products of sheaves of modules are exact: on sections over a weakly contractible object a
product of epimorphisms is a product of surjections of modules. -/
lemma hasExactLimitsOfShape_discrete_of_forall_exists (β : Type w)
    [HasLimitsOfShape (Discrete β) (Sheaf J (ModuleCat.{w} R))] :
    HasExactLimitsOfShape (Discrete β) (Sheaf J (ModuleCat.{w} R)) := by
  have : (lim : (Discrete β ⥤ Sheaf J (ModuleCat.{w} R)) ⥤ _).PreservesEpimorphisms := by
    refine ⟨fun {D D'} f _ ↦ ?_⟩
    rw [epi_iff_of_forall_exists P hP hPW]
    intro W hW
    let E := sheafToPresheaf J (ModuleCat.{w} R) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op W)
    have : ∀ b, Epi ((Functor.whiskerRight f E).app b) := fun b ↦
      (epi_iff_of_forall_exists P hP hPW _).1 inferInstance W hW
    have h := (preservesLimitNatIso (J := Discrete β) E).hom.naturality f
    change Epi (E.map (lim.map f))
    have hE : E.map (lim.map f) = (preservesLimitIso E D).hom ≫
        lim.map (Functor.whiskerRight f E) ≫ (preservesLimitIso E D').inv := by
      rw [← Category.assoc, Iso.eq_comp_inv]
      exact h
    have : Epi (Functor.whiskerRight f E) := NatTrans.epi_of_epi_app _
    have : PreservesFiniteColimits (lim : (Discrete β ⥤ ModuleCat.{w} R) ⥤ _) :=
      HasExactLimitsOfShape.preservesFiniteColimits
    have : Epi (lim.map (Functor.whiskerRight f E)) := lim.map_epi _
    rw [hE]
    infer_instance
  exact hasExactLimitsOfShape_of_preservesEpi _ _

end CategoryTheory.GrothendieckTopology
