/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper

The linear maps `RestrictedProduct.mapAlongLinearMap` and
`RestrictedProduct.inclusionLinearMap` come from
FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard, Ruben Van de Velde

Modified by Worker 217 (2026): adapt the canonical maps of Imperial FLT, commit
923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean:28-91 and
FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:40-88 into one
standalone module with plain Mathlib imports. The module-system keywords are
removed, the module docstring no longer mentions flatness, the
`backward.isDefEq.respectTransparency` option before `lTensor` is dropped
because it is unnecessary at this project's Lean and Mathlib pin, and
`inclusionLinearMap_apply`, the equivalences and all bijectivity results are
omitted. The upstream license is retained at
licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Tensor product distributing over a restricted product

For an `R`-module `M` and a restricted product of `R`-modules `N i`
relative to submodules `L i`, we construct the natural `R`-linear (and
`M`-linear) map `M ⊗_R ∏'ᵢ [N i, L i] → ∏'ᵢ [M ⊗_R N i, M ⊗_R L i]`.
-/

open RestrictedProduct

section modules

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {S₁ : ι₁ → Type*} {S₂ : ι₂ → Type*}
variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]
variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}
variable (f : ι₂ → ι₁) (hf : Filter.Tendsto f 𝓕₂ 𝓕₁)
variable {A : Type*} [Semiring A]
variable [Π i, AddCommMonoid (R₁ i)] [Π i, AddCommMonoid (R₂ i)] [Π i, Module A (R₁ i)]
    [Π i, Module A (R₂ i)] [∀ i, AddSubmonoidClass (S₁ i) (R₁ i)]
    [∀ i, AddSubmonoidClass (S₂ i) (R₂ i)] [∀ i, SMulMemClass (S₁ i) A (R₁ i)]
    [∀ i, SMulMemClass (S₂ i) A (R₂ i)]
    (φ : ∀ j, R₁ (f j) →ₗ[A] R₂ j)
    (hφ : ∀ᶠ j in 𝓕₂, Set.MapsTo (φ j) (B₁ (f j)) (B₂ j))

/--
Given two restricted products `Πʳ (i : ι₁), [R₁ i, B₁ i]_[𝓕₁]` and `Πʳ (j : ι₂), [R₂ j, B₂ j]_[𝓕₂]`
of `A`-modules, `RestrictedProduct.mapAlongLinearMap` gives an `A`-linear map between them.
The data needed is a function `f : ι₂ → ι₁` such that `𝓕₂` tends to `𝓕₁` along `f`, and `A`-linear
maps `φ j : R₁ (f j) → R₂ j` sending `B₁ (f j)` into `B₂ j` for an `𝓕₂`-large set of `j`'s.
-/
def RestrictedProduct.mapAlongLinearMap :
    Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →ₗ[A] Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  __ := mapAlongAddMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ
  map_smul' a f := by
    ext i
    apply map_smul (φ i)

@[simp]
lemma RestrictedProduct.mapAlongLinearMap_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlongLinearMap R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

variable (A : Type*) [CommRing A] {ι : Type*} (R : ι → Type*)
  [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] (C : ∀ i, Submodule A (R i))

/-- A linear map version of `RestrictedProduct.inclusion` :
if `𝓕 ≤ 𝓖` then there's a linear map
`Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕]` where the `R i`
are `A`-modules and the `C i` are submodules.
-/
def RestrictedProduct.inclusionLinearMap
     {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕] :=
  mapAlongLinearMap R R id h (fun _ ↦ .id)
  (Filter.Eventually.of_forall <| fun _ _ ↦ id)

end modules

namespace RestrictedProduct

open TensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)]

variable (ℱ : Filter ι) (L : ∀ i, Submodule R (N i))

/-- `M ⊗_R (L i)` as an `R`-submodule of `M ⊗_R (N i)`. -/
def rangeLTensor (i : ι) : Submodule R (M ⊗[R] N i) :=
  LinearMap.range (LinearMap.lTensor M ((L i).subtype))

/-- `M ⊗_R (L i)` as an `M`-submodule of `M ⊗_R (N i)`. -/
noncomputable def rangeLTensorLeft (R M : Type*) [CommSemiring R] [CommSemiring M] [Algebra R M]
    {ι : Type*} (N : ι → Type*) [∀ i, Semiring (N i)] [∀ i, Algebra R (N i)]
    (L : ∀ i, Submodule R (N i)) (i : ι) : Submodule M (M ⊗[R] N i) :=
  (TensorProduct.AlgebraTensorModule.lTensor _ _ (L i).subtype).range

/-- The `R`-linear map `φ : M ⊗_R ∏'_i [N i, L i]_[𝓕] → ∏'_i [M ⊗_R (N i), M ⊗_R (L i)]_[𝓕]`
given by `φ (m ⊗ n) i = m ⊗ (n i)`. -/
def lTensor :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ] :=
  have hmap : ∀ (m : M), ∀ᶠ (j : ι) in ℱ, Set.MapsTo
      (TensorProduct.mk R M (N j) m) (L j) (rangeLTensor R M N L j) := by
    intro m
    filter_upwards with i n hn using ⟨m ⊗ₜ[R] ⟨n, hn⟩, rfl⟩
  TensorProduct.lift {
    toFun m := mapAlongLinearMap N (M ⊗[R] N ·) id Filter.tendsto_id
        (fun i ↦ TensorProduct.mk R M (N i) m) (hmap m)
    map_add' m n := by ext; simp
    map_smul' a m := by ext; simp
  }

/-- The `M`-linear map `φ : M ⊗_R ∏'_i [N i, L i]_[𝓕] → ∏'_i [M ⊗_R (N i), M ⊗_R (L i)]_[𝓕]`
given by `φ (m ⊗ n) i = m ⊗ (n i)`. -/
noncomputable def lTensorLeft (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (ℱ : Filter ι)
    (L : ∀ i, Submodule R (N i)) :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[M] Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ] :=
  have hmap : ∀ (m : M), ∀ᶠ (j : ι) in ℱ, Set.MapsTo
      (TensorProduct.mk R M (N j) m) (L j) (rangeLTensorLeft R M N L j) := by
    intro m
    filter_upwards with i n hn using ⟨m ⊗ₜ[R] ⟨n, hn⟩, rfl⟩
  let f : (i : ι) → N i →ₗ[R] M ⊗[R] N i := fun i ↦
    { toFun n := 1 ⊗ₜ n, map_add' _ _ := by simp [tmul_add], map_smul' := by simp }
  have (i : ι) : SMulMemClass (Submodule M (M ⊗[R] N i)) R ((fun x ↦ M ⊗[R] N x) i) :=
    .ofIsScalarTower _ _ _ _
  have : IsScalarTower R M Πʳ (i : ι), [M ⊗[R] N i, ↑(rangeLTensorLeft R M N L i)]_[ℱ] := by
    apply IsScalarTower.mk fun r m x ↦ by ext; simp
  (mapAlongLinearMap N (M ⊗[R] N ·) id Filter.tendsto_id f (hmap 1)).liftBaseChange _

@[simp]
lemma lTensor_tmul (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensor R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma lTensorLeft_tmul (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (L : ∀ i, Submodule R (N i))
    (ℱ : Filter ι) (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensorLeft R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) := by
  rw [lTensorLeft, LinearMap.liftBaseChange_tmul, smul_apply, mapAlongLinearMap_apply]
  change m • (_ ⊗ₜ[R] _) = _
  simp [id_eq, smul_tmul' m (1 : M) (f i)]

end RestrictedProduct
