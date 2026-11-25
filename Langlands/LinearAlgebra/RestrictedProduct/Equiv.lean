/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri

Modified in Langlands-lib (2026 and 22 November 2026). The pointwise congruences and the fiber
flattening of Imperial FLT, commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean:33-124 and 520-589, were adapted and the
coordinate lemmas and the linear flattening equivalences were added. On 22 November 2026 the
declarations that the Imperial
project declares under the same names moved to
`Langlands/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean` (staged for Mathlib, Imperial commit
019805815d7da565ed1e9f427b6fbd0cbc9d00d3); the Library's own declarations stay here, under
`Langlands.LinearAlgebra`. The upstream license is retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.Mathlib.Topology.Algebra.RestrictedProduct.Equiv
import Mathlib.LinearAlgebra.Pi

/-!
# Isomorphisms of restricted products: the Library's lemmas and linear flattening

The congruences `Equiv.restrictedProductCongrRight`, `AddEquiv.restrictedProductCongrRight`,
`LinearEquiv.restrictedProductCongrRight` and the flattening `RestrictedProduct.flatten`,
`flattenEquiv`, `flattenEquiv'` are in `Langlands.Mathlib.Topology.Algebra.RestrictedProduct.Equiv`.
This module adds the coordinate lemmas that the Imperial project does not have, and the linear
versions `Langlands.LinearAlgebra.RestrictedProduct.flattenLinearEquiv` and `flattenLinearEquiv'` of the flattening.
-/

open RestrictedProduct

namespace Langlands.LinearAlgebra

section pi_congr_right

variable {ι : Type*} {R₁ : ι → Type*} {R₂ : ι → Type*} {𝓕 : Filter ι}

section add_equiv

variable {S₁ : ι → Type*} {S₂ : ι → Type*}
  [(i : ι) → SetLike (S₁ i) (R₁ i)] [(i : ι) → SetLike (S₂ i) (R₂ i)]
  [(i : ι) → AddMonoid (R₁ i)] [(i : ι) → AddMonoid (R₂ i)]
  [(i : ι) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → AddSubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}

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

end Langlands.LinearAlgebra

namespace Langlands.LinearAlgebra.RestrictedProduct

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

end Langlands.LinearAlgebra.RestrictedProduct
