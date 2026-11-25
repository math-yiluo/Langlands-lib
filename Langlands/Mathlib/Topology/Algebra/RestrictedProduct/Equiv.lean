/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri

Source: the Imperial College London FLT project (github.com/ImperialCollegeLondon/FLT),
commit `0198058` (019805815d7da565ed1e9f427b6fbd0cbc9d00d3),
file `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean`, lines 31-49, 105-126 and 520-589.
Licence: Apache License 2.0; the project's licence is at `licenses/ImperialCollegeLondon-FLT/LICENSE`.

Staged for Mathlib. The declarations of this file have the names that the Imperial project gives them,
and its text except where listed below; they are expected in Mathlib under these names. Delete this
file when the Library's Mathlib has these declarations, and import the Mathlib module instead.

Changes made by the Library (22 November 2026), the text being otherwise the Imperial text:
- the module-system keywords (`module`, `public import`, `@[expose] public section`) are removed, since
  the Library's files are ordinary files;
- taken verbatim: `Equiv.restrictedProductCongrRight` (lines 31-49, without the attribute
  `@[simps]` of line 43), `LinearEquiv.restrictedProductCongrRight` (lines 105-126) and
  `RestrictedProduct.flatten`, `flatten_apply`, `flattenEquiv`, `flatten_equiv_apply`,
  `flatten_equiv_symm_apply`, `flattenEquiv'`, `flatten_equiv'_apply`, `flatten_equiv'_symm_apply`
  (lines 520-589); the other declarations of the Imperial file are not used by the Library and
  are left out (units, rings, reindexing, matrices, products, principal filters);
- Library text, marked `-- Library text:` below: `Equiv.restrictedProductCongrRight_apply`,
  `Equiv.restrictedProductCongrRight_symm_apply` and `AddEquiv.restrictedProductCongrRight_apply`
  are coordinate lemmas `… x i = φ i (x i)`; Imperial generates lemmas of these names by `@[simps]`
  and `@[to_additive (attr := simps! apply)]` with other statements (the whole map), so the
  attribute is dropped and the Library's statements are kept. `AddEquiv.restrictedProductCongrRight`
  is defined directly, as Imperial's `to_additive` of `MulEquiv.restrictedProductCongrRight`
  would bring the multiplicative version, which the Library does not use, and the `simps!` lemma;
- Library text: the inverse laws of `Equiv.restrictedProductCongrRight` are proved by
  `Equiv.symm_apply_apply` and `Equiv.apply_symm_apply`; Imperial's `by ext; simp` (lines 50-51)
  makes no progress in an ordinary (non-`module`) file at this Lean and Mathlib: Mathlib's
  `RestrictedProduct.map_apply` fires only with `backward.isDefEq.respectTransparency` off, and
  the Library sets no such option here;
- the imports are those these declarations need (Imperial: its `Basic` and further Mathlib
  modules); the module docstring is the Library's.
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Isomorphisms of restricted products

Restricted products of factorwise equivalent types, additive monoids or modules are equivalent,
provided the factor equivalences eventually restrict to bijections between the restricting subsets.

A restricted product over `ι₂` of the full products over the fibers of `f : ι → ι₂` maps to the
restricted product over `ι`, and this map is an equivalence when the filter on `ι` is the pullback
of the filter on `ι₂`.
-/

open RestrictedProduct

section pi_congr_right

variable {ι : Type*}
variable {R₁ : ι → Type*} {R₂ : ι → Type*} {S₁ : ι → Type*} {S₂ : ι → Type*}
  [(i : ι) → SetLike (S₁ i) (R₁ i)] [(i : ι) → SetLike (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → Set (R₁ i)} {A₂ : (i : ι) → Set (R₂ i)}
variable {𝓕 : Filter ι}

/-- The equivalence between restricted products on the same index, when
each factor is equivalent, with compatibility on the restricted subsets. -/
def Equiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕] ≃ Πʳ i, [R₂ i, A₂ i]_[𝓕] where
  toFun := map (fun i ↦ φ i) (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo)
  invFun := map (fun i ↦ (φ i).symm)
    (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo ∘ Set.BijOn.equiv_symm)
  -- Library text: the two inverse laws (Imperial: `by ext; simp`, lines 50-51; see the header).
  left_inv x := by ext i; exact (φ i).symm_apply_apply (x i)
  right_inv y := by ext i; exact (φ i).apply_symm_apply (y i)

-- Library text: coordinate lemmas, in place of Imperial's `@[simps]` on the definition above.
@[simp]
lemma Equiv.restrictedProductCongrRight_apply (φ : (i : ι) → R₁ i ≃ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) (x : Πʳ i, [R₁ i, A₁ i]_[𝓕]) (i : ι) :
    Equiv.restrictedProductCongrRight φ hφ x i = φ i (x i) :=
  rfl

@[simp]
lemma Equiv.restrictedProductCongrRight_symm_apply (φ : (i : ι) → R₁ i ≃ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) (y : Πʳ i, [R₂ i, A₂ i]_[𝓕]) (i : ι) :
    (Equiv.restrictedProductCongrRight φ hφ).symm y i = (φ i).symm (y i) :=
  rfl

-- Library text: Imperial obtains `AddEquiv.restrictedProductCongrRight` by `to_additive` from
-- `MulEquiv.restrictedProductCongrRight` (lines 53-66); the Library defines it directly.
section add_equiv

variable [(i : ι) → AddMonoid (R₁ i)] [(i : ι) → AddMonoid (R₂ i)]
  [(i : ι) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → AddSubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}

/-- The `AddEquiv` between restricted products built from `AddEquiv`s on the factors. -/
def AddEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃+ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃+ (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := Equiv.restrictedProductCongrRight (fun i ↦ (φ i).toEquiv) hφ
  map_add' x y := by
    ext i
    exact map_add (φ i) (x i) (y i)

@[simp]
lemma AddEquiv.restrictedProductCongrRight_apply (φ : (i : ι) → R₁ i ≃+ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) (x : Πʳ i, [R₁ i, A₁ i]_[𝓕]) (i : ι) :
    AddEquiv.restrictedProductCongrRight φ hφ x i = φ i (x i) :=
  rfl

end add_equiv

section linear_equiv

variable {T : Type*} [Semiring T]
variable [(i : ι) → AddCommMonoid (R₁ i)] [(i : ι) → AddCommMonoid (R₂ i)]
variable [(i : ι) → Module T (R₁ i)] [(i : ι) → Module T (R₂ i)]
variable [(i : ι) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → AddSubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}
variable [(i : ι) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι) → SMulMemClass (S₂ i) T (R₂ i)]

/-- The `LinearEquiv` between restricted products built from `LinearEquiv`s on the factors. -/
def LinearEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃ₗ[T] R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃ₗ[T] (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := AddEquiv.restrictedProductCongrRight (fun i ↦ (φ i).toAddEquiv)
    (by filter_upwards [hφ]; exact fun i ↦ id)
  map_smul' m x := by
    ext i
    apply map_smul

end linear_equiv

end pi_congr_right

namespace RestrictedProduct

section flatten

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}
variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)

variable (hf : Filter.Tendsto f ℱ 𝒢) in
/-- The canonical map from a restricted product of products over fibres of a map on indexing sets
to the restricted product over the original indexing set. -/
def flatten : Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] →
    Πʳ i, [G i, C i]_[ℱ] :=
  mapAlong _ G f hf (fun i x ↦ x ⟨i, rfl⟩) (by filter_upwards with x y hy using hy ⟨x, rfl⟩ trivial)

@[simp]
lemma flatten_apply (hf : Filter.Tendsto f ℱ 𝒢) (x) (i : ι) :
    flatten C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

variable (hf : Filter.comap f 𝒢 = ℱ)

/-- The canonical bijection from a restricted product of products over fibres of a map on indexing
sets to the restricted product over the original indexing set. -/
def flattenEquiv :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃
    Πʳ i, [G i, C i]_[ℱ] where
  toFun := flatten C (by rw [Filter.tendsto_iff_comap]; exact hf.ge)
  invFun := fun ⟨x, hx⟩ ↦ ⟨fun _ i ↦ x i, by
    rw [← hf, Filter.eventually_comap] at hx
    filter_upwards [hx] with j hj ⟨i, hi⟩ _ using hj i hi⟩
  left_inv := by
    intro ⟨x, hx⟩
    ext _ ⟨i, rfl⟩
    rfl
  right_inv x := by ext i; rfl

@[simp]
lemma flatten_equiv_apply (x) (i : ι) :
    flattenEquiv C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flattenEquiv C hf).symm x i j = x j.1 :=
  rfl

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)

/-- The equivalence given by `flatten` when both restricted products are over the cofinite
filter. -/
def flattenEquiv' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃
    Πʳ i, [G i, C i] :=
  flattenEquiv C <| le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)

@[simp]
lemma flatten_equiv'_apply (x) (i : ι) :
    flattenEquiv' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flattenEquiv' C hf).symm x i j = x j.1 :=
  rfl

end flatten

end RestrictedProduct
