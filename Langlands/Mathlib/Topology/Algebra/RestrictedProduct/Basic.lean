/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard, Ruben Van de Velde

Source: the Imperial College London FLT project (github.com/ImperialCollegeLondon/FLT),
commit `0198058` (019805815d7da565ed1e9f427b6fbd0cbc9d00d3),
file `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean`, lines 8-12 (imports) and 38-88.
Licence: Apache License 2.0; the project's licence is at `licenses/ImperialCollegeLondon-FLT/LICENSE`.

Staged for Mathlib. The declarations of this file have the names that the Imperial project gives them,
and its text except where listed below; they are expected in Mathlib under these names. Delete this
file when the Library's Mathlib has these declarations, and import the Mathlib module instead.

Changes made by the Library (22 November 2026), the text being otherwise the Imperial text:
- the module-system keywords (`module`, `public import`, `@[expose] public section`) are removed, since
  the Library's files are ordinary files;
- only `RestrictedProduct.mapAlongLinearMap`, `RestrictedProduct.mapAlongLinearMap_apply` and
  `RestrictedProduct.inclusionLinearMap` are taken (lines 38-88, verbatim), the declarations of
  the Imperial file that the Library uses; the section is closed after them (`end modules`);
- the module docstring is the Library's.
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Linear maps between restricted products of modules

`RestrictedProduct.mapAlongLinearMap` is the linear version of Mathlib's
`RestrictedProduct.mapAlong`, and `RestrictedProduct.inclusionLinearMap` the linear version of
`RestrictedProduct.inclusion`.
-/

open RestrictedProduct

section modules

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}
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
