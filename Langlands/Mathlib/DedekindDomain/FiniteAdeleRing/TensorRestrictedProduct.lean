/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper

Source: the Imperial College London FLT project (github.com/ImperialCollegeLondon/FLT),
commit `0198058` (019805815d7da565ed1e9f427b6fbd0cbc9d00d3),
file `FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean`, lines 24-91.
Licence: Apache License 2.0; the project's licence is at `licenses/ImperialCollegeLondon-FLT/LICENSE`.

Staged for Mathlib. The declarations of this file have the names that the Imperial project gives them,
and its text except where listed below; they are expected in Mathlib under these names. Delete this
file when the Library's Mathlib has these declarations, and import the Mathlib module instead.

Changes made by the Library (22 November 2026), the text being otherwise the Imperial text:
- the module-system keywords (`module`, `public import`, `@[expose] public section`) are removed, since
  the Library's files are ordinary files;
- the Imperial project keeps this file outside its directory `FLT/Mathlib/` of material sent to
  Mathlib; its declarations are in Mathlib's name space `RestrictedProduct`, and the Library
  stages them for Mathlib like the others;
- taken verbatim (lines 24-91): `RestrictedProduct.rangeLTensor`, `rangeLTensorLeft`, `lTensor`,
  `lTensorLeft`, `lTensor_tmul`, `lTensorLeft_tmul`, the declarations of the Imperial file that the
  Library uses here; the namespace is closed after them. The equivalences `lTensorEquiv`,
  `lTensorEquivLeft` and their `_tmul` lemmas (lines 234-257) keep their Imperial names in
  `Langlands/LinearAlgebra/RestrictedProduct/TensorEquiv.lean`, since there they take bijectivity
  from the Library's own theorem, which is proved from this file; Imperial's `lTensor_bijective` and
  the rest of the file (lines 93-232) are not used by the Library and are left out;
- imports: Mathlib's tensor products and the staged `Basic` (for `mapAlongLinearMap`) in place of
  Imperial's imports of `TensorPi`, `IsDirectLimit` and `IsDirectLimitRestricted`, which the
  declarations kept here do not need; the module docstring is the Library's.
-/
import Mathlib.RingTheory.TensorProduct.Basic
import Langlands.Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Tensor product distributing over a restricted product

For an `R`-module `M` and a restricted product of `R`-modules `N i` relative to submodules `L i`,
the natural `R`-linear (and `M`-linear) map `M ⊗_R ∏'ᵢ [N i, L i] → ∏'ᵢ [M ⊗_R N i, M ⊗_R L i]`.
-/

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

set_option backward.isDefEq.respectTransparency false in
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
