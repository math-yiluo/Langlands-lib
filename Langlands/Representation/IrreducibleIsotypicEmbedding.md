# Irreducible representations inside an isotypic representation

This module works with Mathlib's representations of a
monoid `G` on complex vector spaces in independent universes. A representation
`σ` on `Q` is called `ρA`-isotypic when the supremum of the ranges of the
intertwining maps from `ρA` to `σ` is `⊤` as a submodule of `Q`.

`Langlands.IsotypicEmbedding.isotypic_iff_exists_ne_zero` states that if `Q` is
nonzero and `σ` is `ρA`-isotypic for an irreducible `ρA`, then for any irreducible
`ρW` the representation `σ` is `ρW`-isotypic exactly when it receives a nonzero
intertwining map from `ρW`. This is the algebraic step used at each place in the
local component embedding proof.
[Application to local components](../Automorphic/LocalComponentEmbeddingReduction.md)

## Proof

`exists_ne_zero_of_iSup_range_eq_top` proves one direction. If every
intertwining map from `ρW` is zero, the supremum of their ranges is `⊥`, which
differs from `⊤` by nontriviality of `Q`.

For the other direction, `exists_intertwiningMap_ne_zero_of_isotypic` first
constructs a nonzero intertwining map `e` from `ρW` to `ρA`. It passes to
modules over the monoid algebra `ℂ[G]` using `Representation.asModule` and
`IntertwiningMap.equivLinearMapAsModule`.

1. The `ℂ[G]`-linear map of a nonzero intertwiner `f` from `ρW` is injective
   by `injective_equivLinearMapAsModule`. The domain is simple because `ρW`
   is irreducible, so `LinearMap.injective_or_eq_zero` applies. Its range
   `N` is simple by the linear equivalence with the source. The same
   reasoning gives simplicity of the range of every nonzero map from `ρA`.
2. The set `s` of ranges of those nonzero maps from `ρA` has supremum `⊤`.
   `range_toLinearMap_eq_map_range` compares the original ranges over `ℂ`
   with the ranges over `ℂ[G]` after restriction of scalars and transport
   along `σ.asModuleEquiv`. Isotypy says the original ranges span `Q`.
3. `Submodule.linearEquiv_of_sSup_eq_top` identifies the simple submodule
   `N` with a member of `s`. Composing the two equivalences with the ranges
   gives an `ℂ[G]`-linear equivalence from `ρW.asModule` to `ρA.asModule`.
   Its underlying intertwining map `e` is nonzero by injectivity and
   nontriviality of the source.

In `iSup_range_eq_top_of_isotypic`, `e` is surjective by
`Representation.IsIrreducible.surjective_or_eq_zero` and irreducibility of
`ρA`. For every intertwining map `g` from `ρA` its composite `g.comp e` has the
same range. Thus the ranges of the intertwining maps from `ρW` span `Q`.

## Provenance

This is a derived application of semisimple module theory. The algebraic
input is Mathlib's `Submodule.linearEquiv_of_sSup_eq_top` in
`Mathlib/RingTheory/SimpleModule/Isotypic.lean`. It uses the semisimplicity of
a sum of simple submodules via
`isSemisimpleModule_of_isSemisimpleModule_submodule'` in
`Mathlib/RingTheory/SimpleModule/Basic.lean`.

The application to local factors expands the last sentence of the proof of
Theorem 1 in D. Flath, *Decomposition of representations into tensor products*,
Proc. Sympos. Pure Math. 33, Part 1, AMS, 1979, p. 180 (PDF p. 176), where
Flath uses isotypic restriction to determine the isomorphism class of the
factor. The registered source is `flath-1979-tensor-products`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
