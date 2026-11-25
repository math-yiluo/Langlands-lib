/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.AlgebraicGeometry.FreeComplexBaseLift
import WeilConjectures.AlgebraicGeometry.FreeComplexExtendFamily

/-! # A complex of free modules maps to a resolution
Source: literature/stacks-project/algebra.tex, Tag 00LS
(blueprint: lem-weil-pbc-free-complex-maps-to-resolution).
-/

@[expose] public section

universe u v w

open CategoryTheory

/-- Source: Algebra, Tag 00LS, part (1), lines 17525--17535
(blueprint: lem-weil-pbc-free-complex-maps-to-resolution).
A complex of free modules over `M` maps to an exact resolution of `N`.

Proof in words: exactness at `N` makes `η` surjective and `F 0` is free, hence
projective, so `φ ∘ π` lifts to `α 0` with `η ∘ α 0 = φ ∘ π`. For `α 1`, the map
`α 0 ∘ δ 0` lands in `ker η` because `η ∘ α 0 ∘ δ 0 = φ ∘ π ∘ δ 0 = 0`; exactness at
`N' 0` makes `d 0 : N' 1 → ker η` surjective, and projectivity of `F 1` lifts it.
Inductively, given `α 0, …, α (n+1)` satisfying the identities, `α (n+1) ∘ δ (n+1)`
lands in `ker (d n)` since `d n ∘ α (n+1) ∘ δ (n+1) = α n ∘ δ n ∘ δ (n+1) = 0`;
exactness at `N' (n+1)` and projectivity of `F (n+2)` give `α (n+2)`. Choosing one
extension at each step defines the whole family recursively; only the target is
required to be exact.
-/
theorem free_complex_maps_to_resolution
    (R : Type u) [CommRing R]
    (M N : ModuleCat R) (φ : M ⟶ N)
    (N' : ℕ → ModuleCat R)
    (d : ∀ i : ℕ, N' (i + 1) ⟶ N' i)
    (η : N' 0 ⟶ N)
    (hd0 : d 0 ≫ η = 0)
    (hd : ∀ i : ℕ, d (i + 1) ≫ d i = 0)
    (hη : Function.Surjective η)
    (hex0 : (ShortComplex.mk (d 0) η hd0).Exact)
    (hex : ∀ i : ℕ, (ShortComplex.mk (d (i + 1)) (d i) (hd i)).Exact)
    (F : ℕ → ModuleCat R)
    (δ : ∀ i : ℕ, F (i + 1) ⟶ F i)
    (π : F 0 ⟶ M)
    (hδ0 : (δ 0) ≫ π = 0)
    (hδ : ∀ i : ℕ, (δ (i + 1)) ≫ (δ i) = 0)
    (hfree : ∀ i : ℕ, Module.Free R (F i)) :
    ∃ α : ∀ i : ℕ, F i ⟶ N' i,
      α 0 ≫ η = π ≫ φ ∧
        (∀ i : ℕ, (α (i + 1)) ≫ d i = (δ i) ≫ α i) := by
  obtain ⟨a₀, ha₀⟩ := free_complex_base_lift R M N φ N' η F π hη (hfree 0)
  have hstart : δ 0 ≫ a₀ ≫ η = 0 := by
    rw [ha₀, ← Category.assoc, hδ0, Limits.zero_comp]
  obtain ⟨α, hα₀, hα⟩ :=
    free_complex_extend_family R N N' d η hd0 hd hex0 hex F δ hδ hfree a₀ hstart
  refine ⟨α, ?_, hα⟩
  rw [hα₀, ha₀]
