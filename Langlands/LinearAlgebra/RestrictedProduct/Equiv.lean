/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri

Modified by Worker 205 (2026): adapt the pointwise congruences and the fiber
flattening of Imperial FLT, commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean:33-124 and 520-589,
into one standalone module with plain Mathlib imports. The module-system
keywords are removed. `@[simps]` on `Equiv.restrictedProductCongrRight` is
replaced by explicit coordinate lemmas, and its inverse laws are proved by
`Equiv.symm_apply_apply` and `Equiv.apply_symm_apply` instead of `simp`.
`AddEquiv.restrictedProductCongrRight` is defined directly instead of through
`to_additive` of a `MulEquiv`, with additivity proved by `map_add`. Coordinate
lemmas are added for the additive and linear congruences. Section variables are
regrouped, and the unused flattening variables `H` and `D` are dropped. The
linear wrappers `RestrictedProduct.flattenLinearEquiv` and
`flattenLinearEquiv'` with their coordinate lemmas are new. The
multiplicative, unit, ring, matrix, product, principal-filter, reindexing and
other equivalences of the source file are omitted. The upstream license is
retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Isomorphisms of restricted products

Restricted products of factorwise equivalent types, additive monoids or
modules are equivalent, provided the factor equivalences eventually restrict
to bijections between the restricting subsets.

A restricted product over `ι₂` of the full products over the fibers of
`f : ι → ι₂` maps to the restricted product over `ι`, and this map is an
equivalence when the filter on `ι` is the pullback of the filter on `ι₂`.
-/

open RestrictedProduct

section pi_congr_right

variable {ι : Type*} {R₁ : ι → Type*} {R₂ : ι → Type*} {𝓕 : Filter ι}

section equiv

variable {A₁ : (i : ι) → Set (R₁ i)} {A₂ : (i : ι) → Set (R₂ i)}

/-- The equivalence between restricted products on the same index, when
each factor is equivalent, with compatibility on the restricted subsets. -/
def Equiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕] ≃ Πʳ i, [R₂ i, A₂ i]_[𝓕] where
  toFun := map (fun i ↦ φ i) (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo)
  invFun := map (fun i ↦ (φ i).symm)
    (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo ∘ Set.BijOn.equiv_symm)
  left_inv x := by ext i; exact (φ i).symm_apply_apply (x i)
  right_inv y := by ext i; exact (φ i).apply_symm_apply (y i)

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

end equiv

section add_equiv

variable {S₁ : ι → Type*} {S₂ : ι → Type*}
  [(i : ι) → SetLike (S₁ i) (R₁ i)] [(i : ι) → SetLike (S₂ i) (R₂ i)]
  [(i : ι) → AddMonoid (R₁ i)] [(i : ι) → AddMonoid (R₂ i)]
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

@[simp]
lemma AddEquiv.restrictedProductCongrRight_symm_apply (φ : (i : ι) → R₁ i ≃+ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) (y : Πʳ i, [R₂ i, A₂ i]_[𝓕]) (i : ι) :
    (AddEquiv.restrictedProductCongrRight φ hφ).symm y i = (φ i).symm (y i) :=
  rfl

end add_equiv

section linear_equiv

variable {S₁ : ι → Type*} {S₂ : ι → Type*}
  [(i : ι) → SetLike (S₁ i) (R₁ i)] [(i : ι) → SetLike (S₂ i) (R₂ i)]
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

@[simp]
lemma LinearEquiv.restrictedProductCongrRight_apply (φ : (i : ι) → R₁ i ≃ₗ[T] R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) (x : Πʳ i, [R₁ i, A₁ i]_[𝓕]) (i : ι) :
    LinearEquiv.restrictedProductCongrRight φ hφ x i = φ i (x i) :=
  rfl

@[simp]
lemma LinearEquiv.restrictedProductCongrRight_symm_apply (φ : (i : ι) → R₁ i ≃ₗ[T] R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) (y : Πʳ i, [R₂ i, A₂ i]_[𝓕]) (i : ι) :
    (LinearEquiv.restrictedProductCongrRight φ hφ).symm y i = (φ i).symm (y i) :=
  rfl

end linear_equiv

end pi_congr_right

namespace RestrictedProduct

section flatten

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G : ι → Type*}
    {C : (i : ι) → Set (G i)}
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

section flatten_linear

variable {ι : Type*} {ℱ : Filter ι} {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂}
variable {T : Type*} [Semiring T]
    {G : ι → Type*} [(i : ι) → AddCommMonoid (G i)] [(i : ι) → Module T (G i)]
variable (C : (i : ι) → Submodule T (G i))

variable (hf : Filter.comap f 𝒢 = ℱ)

/-- The `T`-linear version of `flattenEquiv` when the restricting subsets are submodules. On the
fibre side the restricting submodule is the product submodule `Submodule.pi Set.univ`. -/
def flattenLinearEquiv :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Submodule.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃ₗ[T]
    Πʳ i, [G i, C i]_[ℱ] where
  __ := flattenEquiv (fun i ↦ (C i : Set (G i))) hf
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma flattenLinearEquiv_apply (x) (i : ι) :
    flattenLinearEquiv C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flattenLinearEquiv_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flattenLinearEquiv C hf).symm x i j = x j.1 :=
  rfl

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)

/-- The `T`-linear version of `flattenEquiv'`: `flattenLinearEquiv` when both restricted
products are over the cofinite filter. -/
def flattenLinearEquiv' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Submodule.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃ₗ[T]
    Πʳ i, [G i, C i] :=
  flattenLinearEquiv C <|
    le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)

@[simp]
lemma flattenLinearEquiv'_apply (x) (i : ι) :
    flattenLinearEquiv' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flattenLinearEquiv'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flattenLinearEquiv' C hf).symm x i j = x j.1 :=
  rfl

end flatten_linear

end RestrictedProduct
