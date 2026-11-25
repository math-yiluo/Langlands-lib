/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-!
# Functorial complex embeddings through injective subobjects

Source: Stacks Project, Injectives, Lemma `lemma-functorial-injective`
(blueprint: lem-pur-kinjective-functorial-injective).
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CochainComplex

/-- Source: Stacks Project, Injectives, Lemma `lemma-functorial-injective`
(blueprint: lem-pur-kinjective-functorial-injective).
In a Grothendieck abelian category there is a functorial termwise monomorphic
quasi-isomorphism into a complex, factoring in each degree through an injective subobject.
The subobject is represented by the monomorphism `b` from the injective object `I`.

Proof:
1. By `lem-weil-pbc-grothendieck-functorial-injective-embedding`, choose functorial
   injective embeddings `i : id → I`. Set `J(M)^n = I(M^n) ⊕ I(M^(n+1))`, with
   differential `(x,y) ↦ (y,0)`. The maps `(i, i ∘ d)` define a natural termwise
   monomorphism `u : M → J(M)`. Let `v : J(M) → Q(M)` be its cokernel.
2. Take `N(M)` to be the cone of `v` shifted by `-1`. Its degree `n` term is
   `Q(M)^(n-1) ⊕ J(M)^n`, with differential matrix `[-d_Q, -v; 0, d_J]`.
   The natural map `j = (0,u)` is termwise monic, and factors through the subobject
   `0 ⊕ J(M)^n`. This subobject is injective, being a finite sum of injectives.
3. The quotient of `N(M)` by `j(M)` is the shifted cone of the identity of `Q(M)`.
   In degree `n` its terms are `Q(M)^(n-1) ⊕ Q(M)^n`, its differential is
   `[-d_Q, -1; 0, d_Q]`, and `h(q,q') = (0,-q)` contracts it: `dh + hd = id`.
   Thus it is acyclic. By `lem-weil-pbc-complex-ses-homology-long-exact`, the short
   exact sequence with this quotient makes `j` a quasi-isomorphism. All constructions
   are natural in `M`, giving the functor `N` and the natural transformation `j`. -/
theorem exists_functorial_injective_complex_embedding
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C] :
    ∃ (N : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
      (j : 𝟭 (CochainComplex C ℤ) ⟶ N),
      ∀ (M : CochainComplex C ℤ),
        (∀ (n : ℤ), Mono ((j.app M).f n)) ∧ QuasiIso (j.app M) ∧
          ∀ (n : ℤ), ∃ (I : C) (a : M.X n ⟶ I) (b : I ⟶ (N.obj M).X n),
            Injective I ∧ Mono b ∧ a ≫ b = (j.app M).f n :=
  ⟨kInjectiveResolutionFunctor.{v} C, toKInjectiveResolution.{v} C, fun M ↦
    have h := monoQuasiIso_toKInjectiveResolution_app.{v} C M
    have := h.1
    ⟨fun _ ↦ inferInstance, h.2, fun _ ↦
      ⟨_, _, 𝟙 _, inferInstance, inferInstance, Category.comp_id _⟩⟩⟩

end CochainComplex
