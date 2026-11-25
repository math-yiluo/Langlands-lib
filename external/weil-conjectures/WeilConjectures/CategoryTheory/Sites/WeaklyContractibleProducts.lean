/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible

/-!
# Products of sheaves of modules on sites with enough weakly contractible objects

If every object of a site is covered by weakly contractible objects, epimorphisms of sheaves of
modules are detected by surjectivity on sections over weakly contractible objects. Since
sections commute with products, a tower of epimorphisms satisfies the
Mittag-Leffler property `R¹ lim = 0`, in the form that `1 - t` is an epimorphism on a product
of the tower (Stacks 0947, 091J).

## Main results

- `CategoryTheory.GrothendieckTopology.epi_iff_of_forall_exists`: epimorphisms of sheaves of
  modules are detected on sections over weakly contractible objects.
- `CategoryTheory.GrothendieckTopology.epi_one_sub_of_forall_exists`: for a tower of
  epimorphisms `F`, the map `1 - t` on a product `∏ Fₙ` is an epimorphism.
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
/-- If every object of the site is covered by weakly contractible objects satisfying `P`, a
morphism of sheaves of modules is an epimorphism if and only if it is surjective on sections
over every object satisfying `P`. -/
lemma epi_iff_of_forall_exists {F G : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ G) :
    Epi f ↔ ∀ W, P W → Epi (f.hom.app (op W)) := by
  rw [← ShortComplex.exact_iff_epi (ShortComplex.mk f (0 : G ⟶ G) comp_zero) rfl,
    exact_iff_of_forall_exists P hP hPW]
  refine forall₂_congr fun W _ ↦ ?_
  rw [ShortComplex.exact_iff_epi _ (by simp)]
  rfl

include hP hPW in
/-- **Mittag-Leffler for towers of epimorphisms.** If every object of the site is covered by
weakly contractible objects, then for a tower `F` of sheaves of modules with epimorphic
transitions, the map `1 - t` on a product `∏ Fₙ` is an epimorphism, where `t` has components
`∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`: on sections over a weakly contractible object this is
`ModuleCat.epi_one_sub_of_epi`. -/
lemma epi_one_sub_of_forall_exists {F : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} R)}
    {Pf : Fan fun n : ℕ ↦ F.obj (op n)} (hPf : IsLimit Pf) (t : Pf.pt ⟶ Pf.pt)
    (ht : ∀ n : ℕ, t ≫ Pf.proj n = Pf.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) : Epi (𝟙 Pf.pt - t) := by
  rw [epi_iff_of_forall_exists P hP hPW]
  intro W hW
  let E := sheafToPresheaf J (ModuleCat.{w} R) ⋙ (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op W)
  have hPf' : IsLimit (Fan.mk Pf.pt Pf.proj) :=
    IsLimit.ofIsoLimit hPf (Cone.ext (Iso.refl _) fun ⟨_⟩ ↦ (Category.id_comp _).symm)
  have := ModuleCat.epi_one_sub_of_epi (F := F ⋙ E)
    (isLimitFanMkObjOfIsLimit E _ _ hPf') (E.map t)
    (fun n ↦ by simpa [E] using congrArg E.map (ht n))
    (fun n ↦ (epi_iff_of_forall_exists P hP hPW _).1 (hF n) W hW)
  change Epi (E.map (𝟙 Pf.pt - t))
  rw [E.map_sub, E.map_id]
  exact this

end CategoryTheory.GrothendieckTopology
