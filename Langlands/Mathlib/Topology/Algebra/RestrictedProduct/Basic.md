# Linear maps between restricted products of modules (stand-in for Mathlib)

Module `Langlands.Mathlib.Topology.Algebra.RestrictedProduct.Basic`. It declares, in the root name
space `RestrictedProduct`, the linear-map versions of two maps of Mathlib's
`Mathlib.Topology.Algebra.RestrictedProduct.Basic`: `RestrictedProduct.mapAlongLinearMap` (with its
`simp` lemma `RestrictedProduct.mapAlongLinearMap_apply`) and `RestrictedProduct.inclusionLinearMap`.
It imports five Mathlib modules, those of the Imperial file. No topology is used.

## Origin, stand-in status and licence

The file is taken from the Imperial College London FLT project
(github.com/ImperialCollegeLondon/FLT) at commit `0198058` (`019805815d7da565ed1e9f427b6fbd0cbc9d00d3`), file
`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean`, lines 8-12 (imports) and 38-88. The project releases it under the Apache License 2.0; its licence is in
the Library at `licenses/ImperialCollegeLondon-FLT/LICENSE`, and the Lean file keeps the source's
copyright and author lines.

The file is a **stand-in for Mathlib**: the three declarations have the names that the Imperial project gives them, and
are expected in Mathlib under these names. The file is to be deleted when the Library's Mathlib has
these declarations; the modules that use them then import Mathlib's module instead.

Until 22 November 2026 these declarations were in `Langlands/LinearAlgebra/RestrictedProduct/`, ported
from the earlier Imperial commit `923d45174c500aa1d994ba973bac38ea39eacbf7`. The
declarations that the Imperial project declares under the same name were then moved
here, with the Imperial text of commit `0198058` wherever the declaration is the same one, so that this
file can be compared line by line with its source. The header of the Lean file gives the line ranges
taken and every difference.

Differences from the Imperial text: the module-system keywords are removed (the Library's files are
ordinary files); only these three declarations of the Imperial file are taken, the ones the Library
uses, and the section is closed after them (Imperial's root-level `inclusionLinearMap_apply` and the rest
of its file are not used by the Library); the module docstring is the Library's. The declarations' text
is the Imperial text, unchanged.

## Linear restricted-product helpers

The two helpers below are linear-map versions of Mathlib maps. The pinned
Mathlib has `RestrictedProduct.mapAlong`, `mapAlongMonoidHom`, the
`to_additive` version `mapAlongAddMonoidHom`, `mapAlongRingHom` and
`inclusion`. It has no linear-map version of these. A text search of the
pinned Mathlib sources finds no `mapAlongLinearMap`, `inclusionLinearMap` or
`rangeLTensor`, and no `LinearMap` or `→ₗ` in
`Mathlib/Topology/Algebra/RestrictedProduct/`. The Library's `Langlands.RestrictedTensor`
modules construct restricted tensor products of vector spaces with reference
vectors, which is a different construction.

### `mapAlongLinearMap`

The full signature has seven universe parameters. Its arguments are:

- index types `ι₁ : Type u_1` and `ι₂ : Type u_2`, explicit coordinate
  families `R₁ : ι₁ → Type u_3` and `R₂ : ι₂ → Type u_4`, and filters
  `𝓕₁ : Filter ι₁` and `𝓕₂ : Filter ι₂`;
- subobject families `S₁ : ι₁ → Type u_5` and `S₂ : ι₂ → Type u_6`, with
  `SetLike`, `AddSubmonoidClass` and `SMulMemClass … A …` instances, and
  chosen subobjects `B₁ i : S₁ i` and `B₂ j : S₂ j`;
- an explicit `f : ι₂ → ι₁` and an explicit proof of
  `Filter.Tendsto f 𝓕₂ 𝓕₁`;
- a semiring `A : Type u_7`, additive commutative monoids `R₁ i` and `R₂ j`,
  and `A`-module structures on them;
- explicit `A`-linear maps `φ j : R₁ (f j) →ₗ[A] R₂ j`, together with an
  explicit proof that `Set.MapsTo (φ j) (B₁ (f j)) (B₂ j)` holds for
  `𝓕₂`-eventually all `j`.

The result is an `A`-linear map
`Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →ₗ[A] Πʳ j, [R₂ j, B₂ j]_[𝓕₂]`.
Its underlying additive map is Mathlib's `mapAlongAddMonoidHom` built from
the same data. Additivity therefore comes from Mathlib. The new field
`map_smul'` is checked coordinatewise with `map_smul (φ i)`.

`mapAlongLinearMap_apply` is the `simp` lemma

```
mapAlongLinearMap R₁ R₂ f hf φ hφ x j = φ j (x (f j)),
```

and it holds by `rfl`.

Both declarations are used by `Langlands.Mathlib.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct`. `lTensor` and `lTensorLeft` are
built from `mapAlongLinearMap`, and the proof of `lTensorLeft_tmul` rewrites
with `mapAlongLinearMap_apply`. In the source, the later proof of
`lTensor_bijective` also uses `mapAlongLinearMap_apply`.

### `inclusionLinearMap`

Its arguments are `A : Type u_1` with `[CommRing A]`, an implicit
`ι : Type u_2`, an explicit `R : ι → Type u_3` with
`[∀ i, AddCommGroup (R i)] [∀ i, Module A (R i)]`, explicit
`A`-submodules `C i : Submodule A (R i)`, implicit filters `𝓕 𝓖 : Filter ι`,
and an explicit proof `h : 𝓕 ≤ 𝓖`. The result is

```
inclusionLinearMap A R C h : Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕].
```

It is `mapAlongLinearMap R R id h (fun _ ↦ LinearMap.id) _`. The `MapsTo`
side condition holds for every index, because the identity maps each `C i`
into itself. Coordinatewise, it is the identity, the linear form of Mathlib's
`RestrictedProduct.inclusion`.

No declaration of the Library uses `inclusionLinearMap`. It is retained as
the one linear restricted-product definition of the source's direct-limit
argument. In
the source, `lTensor_bijective` writes `M ⊗[R] Πʳ i, [N i, L i]_[ℱ]` as a
direct limit over the principal filters `𝓟 s` with `s ∈ ℱ`. The transition
maps of that direct limit are `inclusionLinearMap`
(`TensorRestrictedProduct.lean` lines 174–194, and
`IsDirectLimitRestricted.lean` lines 59–102). As a published definition it
can be named by Prop statements.

## Checks

The module builds with Lean 4.35.0 and Mathlib `56a0058` (the Library's pin, also the Imperial
project's at `0198058`). The types of the three declarations are the same as before the move
(compared declaration by declaration, binders and statement, on 22 November 2026).
