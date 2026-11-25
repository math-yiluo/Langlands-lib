/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Sections of constant sheaves

Let `J` be a Grothendieck topology on `C` and `A` a concrete category for which `J.W` is
the class of locally bijective morphisms
(`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`),
so that the sheafification map `toSheafify J P` of every presheaf `P` is locally injective and
locally surjective. For the constant presheaf at `N : A` this gives:

- finitely many sections of the constant sheaf `N_C` over `U` come, on a common covering
  sieve of `U`, from elements of `N`
  (`CategoryTheory.GrothendieckTopology.exists_mem_forall_exists_toSheafify_const_app_eq`);
- over an object `U` which is not covered by the empty sieve, the map `N ⟶ N_C(U)` is
  injective (`CategoryTheory.GrothendieckTopology.toSheafify_const_app_injective`), the
  constant presheaf having identity restriction maps.

-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A finite intersection of covering sieves is covering. -/
lemma GrothendieckTopology.finset_inf_mem {ι : Type*} {U : C} (s : Finset ι) (S : ι → Sieve U)
    (hS : ∀ i ∈ s, S i ∈ J U) : s.inf S ∈ J U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [J.top_mem U]
  | insert a s _ ih =>
    rw [Finset.inf_insert]
    exact J.intersection_covering (hS a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hS i (Finset.mem_insert_of_mem hi))

/-- A finite intersection of covering sieves is covering. -/
lemma GrothendieckTopology.iInf_mem {ι : Type*} [Finite ι] {U : C} (S : ι → Sieve U)
    (hS : ∀ i, S i ∈ J U) : ⨅ i, S i ∈ J U := by
  have := Fintype.ofFinite ι
  have h : ⨅ i, S i = Finset.univ.inf S := by
    rw [Finset.inf_eq_iInf]
    simp
  rw [h]
  exact J.finset_inf_mem _ _ fun i _ ↦ hS i

variable {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [HasWeakSheafify J A] [J.WEqualsLocallyBijective A]

/-- **Finitely many sections of a constant sheaf are locally constant**: for finitely many
sections `x i` of the constant sheaf at `N` over `U`, there is a covering sieve of `U` on
whose members every `x i` is the image of an element of `N`.
(blueprint: `lem-weil-pbc-finite-constant-set-sections-cover`) -/
lemma GrothendieckTopology.exists_mem_forall_exists_toSheafify_const_app_eq (N : A) {U : C}
    {ι : Type*} [Finite ι]
    (x : ι → ToType ((CategoryTheory.sheafify J ((Functor.const Cᵒᵖ).obj N)).obj (op U))) :
    ∃ S ∈ J U, ∀ ⦃V : C⦄ (g : V ⟶ U), S g → ∀ i, ∃ n : ToType N,
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)).app (op V) n =
        (CategoryTheory.sheafify J ((Functor.const Cᵒᵖ).obj N)).map g.op (x i) := by
  refine ⟨⨅ i, Presheaf.imageSieve (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)) (x i),
    J.iInf_mem _ fun i ↦ Presheaf.imageSieve_mem J _ (x i), fun V g hg i ↦ ?_⟩
  have hg' : (⨅ i, Presheaf.imageSieve (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N))
      (x i)) ≤
      Presheaf.imageSieve (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)) (x i) :=
    iInf_le _ i
  exact hg' _ hg

/-- **The constant presheaf embeds into its sheafification over non-degenerate objects**: if
the empty sieve does not cover `U`, then `N ⟶ N_C(U)` is injective, the restriction maps of
the constant presheaf being identities. -/
lemma GrothendieckTopology.toSheafify_const_app_injective (N : A) {U : C}
    (hU : (⊥ : Sieve U) ∉ J U) :
    Function.Injective ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)).app (op U)) := by
  intro x y hxy
  by_contra hne
  refine hU ?_
  have h := Presheaf.equalizerSieve_mem J
    (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)) x y hxy
  convert h
  ext V g
  simp only [Sieve.bot_apply, Presheaf.equalizerSieve_apply, Functor.const_obj_map,
    false_iff]
  exact fun h ↦ hne (by simpa using h)

end CategoryTheory

namespace CategoryTheory

section ModuleCat

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {Λ : Type v'} [Ring Λ] [HasWeakSheafify J (ModuleCat.{v'} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{v'} Λ)] {T : C}

/-- **A morphism between constant sheaves of modules is locally induced by a linear map**,
in the form of sections: for `φ : M_C ⟶ N_C` with `M` finitely generated and any object `T`,
there is a covering sieve `S` of `T` such that over every member `U` of `S` not covered by the
empty sieve, `φ` sends the constant section `m` over `U` to the constant section `f m`, for a
`Λ`-linear map `f : M ⟶ N`. The sections `φ♭(x)` for `x` in a finite generating set of `M` are
lifted to elements of `N` on a common cover; since `N ⟶ N_C(U)` is injective and its range is a
submodule, every `φ♭(m)` then comes from a unique element `f m` of `N`, and `f` is linear. -/
theorem exists_mem_forall_exists_linearMap (M N : ModuleCat.{v'} Λ) [Module.Finite Λ M]
    (φ : (constantSheaf J (ModuleCat.{v'} Λ)).obj M ⟶ (constantSheaf J (ModuleCat.{v'} Λ)).obj N) :
    ∃ S ∈ J T, ∀ ⦃U : C⦄ (g : U ⟶ T), S g → (⊥ : Sieve U) ∉ J U → ∃ f : M ⟶ N, ∀ m : M,
        φ.hom.app (op U) ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) m) =
        (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)).app (op U) (f m) := by
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := Λ) (M := M)
  obtain ⟨S, hS, h⟩ := J.exists_mem_forall_exists_toSheafify_const_app_eq N (U := T)
    (fun m : (t : Set M) ↦ φ.hom.app (op T)
      ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) m.1))
  refine ⟨S, hS, fun U g hg hU ↦ ?_⟩
  choose n hn using h g hg
  have hn' (m : (t : Set M)) :
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)).app (op U) (n m) =
        φ.hom.app (op U)
          ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) m.1) := by
    rw [hn]
    erw [← NatTrans.naturality_apply φ.hom,
      ← NatTrans.naturality_apply (CategoryTheory.toSheafify J _)]
    rfl
  clear hn
  have hinj := J.toSheafify_const_app_injective N hU
  let ιN := ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)).app (op U)).hom
  let L := (φ.hom.app (op U)).hom ∘ₗ
    ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U)).hom
  have hle : LinearMap.range L ≤ LinearMap.range ιN := by
    rw [LinearMap.range_eq_map, ← ht, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨n ⟨m, hm⟩, hn' ⟨m, hm⟩⟩
  let e := LinearEquiv.ofInjective ιN hinj
  refine ⟨ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ
    L.codRestrict _ fun m ↦ hle (LinearMap.mem_range_self L m)), fun m ↦ ?_⟩
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨L m, hle (LinearMap.mem_range_self L m)⟩)
  rw [LinearEquiv.ofInjective_apply] at h
  exact h.symm

end ModuleCat

end CategoryTheory
