/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Weakly contractible objects of a site

An object `W` of a site `(C, J)` is weakly contractible (Stacks 090M) if every locally
surjective morphism of sheaves of sets is surjective on sections over `W`.

## Main results

- `CategoryTheory.GrothendieckTopology.IsWeaklyContractible`: the definition.
- `CategoryTheory.GrothendieckTopology.isWeaklyContractible_of_forall_mem`: if every covering
  sieve of `W` contains a covering family of pairwise disjoint monomorphisms, then `W` is
  weakly contractible.
- `CategoryTheory.GrothendieckTopology.isZero_sheaf_iff_of_forall_exists`,
  `CategoryTheory.GrothendieckTopology.exact_iff_of_forall_exists`: if every object is covered
  by weakly contractible objects satisfying `P`, vanishing of sheaves of modules and exactness
  of short complexes of sheaves of modules are detected on sections over objects satisfying `P`
  (Stacks 0947).
-/

@[expose] public section

universe w w' v u

open Opposite

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Stacks 090M. An object `W` is weakly contractible if every locally surjective morphism of
sheaves of sets is surjective on sections over `W`. -/
@[stacks 090M]
def IsWeaklyContractible (W : C) : Prop :=
  ∀ ⦃F G : Sheaf J (Type w)⦄ (f : F ⟶ G), Sheaf.IsLocallySurjective f →
    Function.Surjective (f.hom.app (op W))

variable {J}

/-- If every covering sieve `S` of `W` contains the members of a covering family of
monomorphisms `f i : Y i ⟶ W` which are pairwise disjoint (any object mapping compatibly to
`Y i` and `Y j` with `i ≠ j` is covered by the empty sieve), then `W` is weakly contractible:
local sections over the `Y i` can be glued to a section over `W`. -/
lemma isWeaklyContractible_of_forall_mem {W : C}
    (h : ∀ S ∈ J W, ∃ (ι : Type w') (Y : ι → C) (f : ∀ i, Y i ⟶ W),
      Sieve.ofArrows Y f ∈ J W ∧ (∀ i, S (f i)) ∧ (∀ i, Mono (f i)) ∧
      ∀ i j, i ≠ j → ∀ (Z : C) (a : Z ⟶ Y i) (b : Z ⟶ Y j), a ≫ f i = b ≫ f j → ⊥ ∈ J Z) :
    J.IsWeaklyContractible.{w} W := by
  intro F G φ hφ s
  obtain ⟨ι, Y, f, hcov, hS, hmono, hdisj⟩ := h _ (Presheaf.imageSieve_mem J φ.hom (U := op W) s)
  choose t ht using hS
  have hF := ((isSheaf_iff_isSheaf_of_type J F.obj).1 F.property).isSheafFor _ hcov
  rw [Presieve.isSheafFor_arrows_iff] at hF
  obtain ⟨x, hx, -⟩ := hF (fun i ↦ t i) (by
    intro i j Z a b hab
    by_cases hij : i = j
    · subst hij
      obtain rfl := (cancel_mono (f i)).1 hab
      rfl
    · exact Sheaf.isSeparated F Z ⊥ (hdisj i j hij Z a b hab) _ _ (by simp))
  refine ⟨x, Sheaf.isSeparated G W _ hcov _ _ ?_⟩
  rintro Z g ⟨_, a, _, ⟨i⟩, rfl⟩
  simp only [op_comp, Functor.map_comp, types_comp_apply]
  rw [← NatTrans.naturality_apply φ.hom, hx, ← ht i]

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory

open Limits

/-- For a functor `F` preserving the kernel of `S.g`, the image of `S` under `F` is exact if
and only if `F` maps the canonical morphism `S.X₁ ⟶ kernel S.g` to an epimorphism. -/
lemma ShortComplex.exact_map_iff_epi_map_kernel_lift {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (S : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesLimit (parallelPair S.g 0) F] :
    (S.map F).Exact ↔ Epi (F.map (kernel.lift S.g S.f S.zero)) := by
  rw [exact_iff_epi_kernel_lift, ← epi_comp_iff_of_isIso _ (kernelComparison S.g F),
    map_lift_kernelComparison]
  rfl

end CategoryTheory

namespace CategoryTheory.GrothendieckTopology

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Type*} [Ring R] (P : C → Prop)

/-- If every object of the site is covered by objects satisfying `P`, a sheaf of modules
vanishes if and only if its sections over all objects satisfying `P` vanish. -/
lemma isZero_sheaf_iff_of_forall_exists [J.HasSheafCompose (forget (ModuleCat.{w} R))]
    (hP : ∀ V : C, ∃ (ι : Type w') (W : ι → C) (f : ∀ i, W i ⟶ V),
      (∀ i, P (W i)) ∧ Sieve.ofArrows W f ∈ J V)
    (F : Sheaf J (ModuleCat.{w} R)) :
    IsZero F ↔ ∀ W, P W → Subsingleton (F.obj.obj (op W)) := by
  refine ⟨fun h W _ ↦ ModuleCat.subsingleton_of_isZero
    (((sheafToPresheaf J _ ⋙ (evaluation Cᵒᵖ _).obj (op W))).map_isZero h), fun h ↦ ?_⟩
  refine Sheaf.isZero_of_isZero_obj F fun V ↦ ?_
  obtain ⟨ι, W, f, hW, hcov⟩ := hP V.unop
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y ↦ ?_⟩
  refine Sheaf.isSeparated F V.unop _ hcov x y ?_
  rintro Z g ⟨_, a, _, ⟨i⟩, rfl⟩
  have := h _ (hW i)
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    Subsingleton.elim (F.obj.map (f i).op x) (F.obj.map (f i).op y)]

/-- **Stacks 0947 (1).** If every object of the site is covered by weakly contractible objects
satisfying `P`, a short complex of sheaves of modules is exact if and only if its sections over
every object satisfying `P` form an exact short complex of modules. -/
lemma exact_iff_of_forall_exists [HasSheafify J (ModuleCat.{w} R)]
    [J.WEqualsLocallyBijective (ModuleCat.{w} R)] [J.HasSheafCompose (forget (ModuleCat.{w} R))]
    (hP : ∀ V : C, ∃ (ι : Type w') (W : ι → C) (f : ∀ i, W i ⟶ V),
      (∀ i, P (W i)) ∧ Sieve.ofArrows W f ∈ J V)
    (hPW : ∀ W, P W → J.IsWeaklyContractible.{w} W)
    (S : ShortComplex (Sheaf J (ModuleCat.{w} R))) :
    S.Exact ↔ ∀ W, P W → (S.map (sheafToPresheaf J _ ⋙ (evaluation Cᵒᵖ _).obj (op W))).Exact := by
  have key (W : C) : (S.map (sheafToPresheaf J _ ⋙ (evaluation Cᵒᵖ _).obj (op W))).Exact ↔
      Function.Surjective ((kernel.lift S.g S.f S.zero).hom.app (op W)) := by
    rw [ShortComplex.exact_map_iff_epi_map_kernel_lift, ModuleCat.epi_iff_surjective]
    rfl
  simp_rw [key]
  rw [ShortComplex.exact_iff_epi_kernel_lift, ← Sheaf.isLocallySurjective_iff_epi']
  refine ⟨fun h W hW ↦ hPW W hW ((sheafCompose J (forget _)).map _)
    ((Presheaf.isLocallySurjective_iff_whisker_forget J _).1 h), fun h ↦ ⟨fun {V} s ↦ ?_⟩⟩
  obtain ⟨ι, W, f, hW, hcov⟩ := hP V
  refine J.superset_covering ?_ hcov
  rintro _ _ ⟨_, a, _, ⟨i⟩, rfl⟩
  exact (Presheaf.imageSieve _ s).downward_closed (h _ (hW i) _) a

end CategoryTheory.GrothendieckTopology
