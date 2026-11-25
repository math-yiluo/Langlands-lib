/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Finite disjoint covers in a site

A family of morphisms `f i : Y i ⟶ W` in a site is a *disjoint cover*
(`CategoryTheory.GrothendieckTopology.IsDisjointCover`) if it generates a covering sieve, consists
of monomorphisms, and is pairwise disjoint: any object mapping compatibly to `Y i` and `Y j` with
`i ≠ j` is covered by the empty sieve. For a sheaf `F`, sections over the `Y i` then glue
uniquely, i.e. `F(W) ≅ ∏ F(Y i)`.

An object `W` *has finite disjoint refinements*
(`CategoryTheory.GrothendieckTopology.HasFiniteDisjointRefinements`) if every covering sieve of
`W` contains the members of a finite disjoint cover of `W`. This holds for affine objects of the
pro-étale site whose underlying ring is w-contractible. Over such an object, a locally surjective
morphism `P ⟶ Q` of presheaves of modules with `Q` separated is surjective on sections over `W`
as soon as sections of `P` over the members of finite disjoint covers of `W` glue
(`CategoryTheory.Presheaf.surjective_app_of_hasFiniteDisjointRefinements`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A family of morphisms `f i : Y i ⟶ W` is a disjoint cover of `W` if it generates a covering
sieve, consists of monomorphisms, and is pairwise disjoint: any object mapping compatibly to
`Y i` and `Y j` with `i ≠ j` is covered by the empty sieve. -/
structure IsDisjointCover {W : C} {ι : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ W) : Prop where
  ofArrows_mem : Sieve.ofArrows Y f ∈ J W
  mono (i : ι) : Mono (f i)
  bot_mem (i j : ι) (hij : i ≠ j) {Z : C} (a : Z ⟶ Y i) (b : Z ⟶ Y j) (h : a ≫ f i = b ≫ f j) :
    ⊥ ∈ J Z

/-- An object `W` has finite disjoint refinements if every covering sieve of `W` contains the
members of a finite disjoint cover of `W`. -/
def HasFiniteDisjointRefinements (W : C) : Prop :=
  ∀ S ∈ J W, ∃ (n : ℕ) (Y : Fin n → C) (f : ∀ i, Y i ⟶ W), J.IsDisjointCover f ∧ ∀ i, S (f i)

variable {J}

namespace IsDisjointCover

variable {R : Type*} [Ring R] {W : C} {ι : Type*} {Y : ι → C} {f : ∀ i, Y i ⟶ W}

/-- Sections of a sheaf of modules over the members of a disjoint cover glue. -/
lemma exists_map_eq [J.HasSheafCompose (forget (ModuleCat.{w} R))] (hf : J.IsDisjointCover f)
    (F : Sheaf J (ModuleCat.{w} R)) (t : ∀ i, F.obj.obj (op (Y i))) :
    ∃ x : F.obj.obj (op W), ∀ i, F.obj.map (f i).op x = t i := by
  have hF := ((isSheaf_iff_isSheaf_of_type J _).1
    ((sheafCompose J (forget _)).obj F).property).isSheafFor _ hf.ofArrows_mem
  rw [Presieve.isSheafFor_arrows_iff] at hF
  obtain ⟨x, hx, -⟩ := hF t (by
    intro i j Z a b hab
    by_cases hij : i = j
    · subst hij
      have := hf.mono i
      obtain rfl := (cancel_mono (f i)).1 hab
      rfl
    · exact Sheaf.isSeparated F Z ⊥ (hf.bot_mem i j hij a b hab) _ _ (by simp))
  exact ⟨x, hx⟩

end IsDisjointCover

end GrothendieckTopology

namespace Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type*} [Ring R]

/-- Let `f i : Y i ⟶ W` be a finite family of morphisms and `P` a presheaf of modules. If, for
each `i`, every element `z` of a generating set of `P(Y i)` is the restriction of a section over
`W` whose restrictions to the other `Y k` vanish, then every family of sections over the `Y i`
is the family of restrictions of a section over `W`. -/
lemma exists_map_eq_of_exists_map_eq_single {P : Cᵒᵖ ⥤ ModuleCat.{w} R} {W : C} {ι : Type*}
    [Finite ι] [DecidableEq ι] {Y : ι → C} (f : ∀ i, Y i ⟶ W)
    (G : ∀ i, Set (P.obj (op (Y i)))) (hG : ∀ i, Submodule.span R (G i) = ⊤)
    (h : ∀ i, ∀ z ∈ G i, ∃ x : P.obj (op W), ∀ k,
      P.map (f k).op x = Pi.single (M := fun k ↦ P.obj (op (Y k))) i z k)
    (t : ∀ i, P.obj (op (Y i))) : ∃ x : P.obj (op W), ∀ i, P.map (f i).op x = t i := by
  let res : P.obj (op W) →ₗ[R] ∀ k, P.obj (op (Y k)) :=
    LinearMap.pi fun k ↦ (P.map (f k).op).hom
  have key (i : ι) : ⊤ ≤ (LinearMap.range res).comap
      (LinearMap.single R (fun k ↦ P.obj (op (Y k))) i) := by
    rw [← hG i, Submodule.span_le]
    intro z hz
    obtain ⟨x, hx⟩ := h i z hz
    exact ⟨x, funext hx⟩
  have := Fintype.ofFinite ι
  obtain ⟨x, hx⟩ : t ∈ LinearMap.range res := by
    rw [← Finset.univ_sum_single t]
    exact Submodule.sum_mem _ fun i _ ↦ key i Submodule.mem_top
  exact ⟨x, fun i ↦ congrFun hx i⟩

/-- Let `W` be an object with finite disjoint refinements and `φ : P ⟶ Q` a locally surjective
morphism of presheaves of modules with `Q` separated. If sections of `P` over the members of
every finite disjoint cover of `W` glue, then `φ` is surjective on sections over `W`. -/
lemma surjective_app_of_hasFiniteDisjointRefinements [J.HasSheafCompose (forget (ModuleCat.{w} R))]
    {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (φ : P ⟶ Q) [IsLocallySurjective J φ]
    (hQ : IsSeparated J Q) {W : C} (hW : J.HasFiniteDisjointRefinements W)
    (hP : ∀ (n : ℕ) (Y : Fin n → C) (f : ∀ i, Y i ⟶ W), J.IsDisjointCover f →
      ∀ t : ∀ i, P.obj (op (Y i)), ∃ x : P.obj (op W), ∀ i, P.map (f i).op x = t i) :
    Function.Surjective (φ.app (op W)) := by
  intro y
  obtain ⟨n, Y, f, hf, hS⟩ := hW _ (imageSieve_mem J φ y)
  choose t ht using hS
  obtain ⟨x, hx⟩ := hP n Y f hf t
  refine ⟨x, hQ _ _ hf.ofArrows_mem _ _ ?_⟩
  rintro Z g ⟨_, a, _, ⟨i⟩, rfl⟩
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← NatTrans.naturality_apply φ, hx, ht i]

end Presheaf

end CategoryTheory
