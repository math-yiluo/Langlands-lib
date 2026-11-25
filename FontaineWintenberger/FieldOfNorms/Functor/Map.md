# Functoriality of the field of norms

Module `FontaineWintenberger.FieldOfNorms.Functor.Map`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For an APF extension `L/K`, the field of norms `FieldOfNorms K L` (written `X_K(L)` in the file) is functorial in `L`. A `K`-isomorphism reindexes the norm-compatible families. A finite separable extension `M ⊆ N` induces a field homomorphism `X_K(M) → X_K(N)`, read off on the "good" finite intermediate fields `D` of `N` (`IsGoodFiniteLayer`: those for which `M ⊗ D → N`, over `D ∩ M`, is an isomorphism). The two combine into a map for any `K`-embedding whose target is finite separable over the image. For the ring structure, `K` satisfies `IsPerfectResidueLocalField` and the extensions are separable, APF and infinite over `K`.

## Definitions

- `FieldOfNorms.mapFun e`, for `e : L ≃ₐ[K] M`: the reindexing as a function; the coordinate at `E ⊆ M` is `e` applied to the coordinate at `e⁻¹(E)`. It needs only fields and algebras.
- `FieldOfNorms.mapEquiv e`: the same as a ring isomorphism `X_K(L) ≃+* X_K(M)`.
- `FieldOfNorms.aut`: the homomorphism from `L ≃ₐ[K] L` to ring automorphisms of `X_K(L)` (Remark 3.2.4).
- `FieldOfNorms.pullbackCoord`: the coordinate of a family of `M` at `D ∩ M`, viewed in `D`.
- `FieldOfNorms.inclusion₀`: the multiplicative map `X_K(M) →*₀ X_K(N)`, defined without APF hypotheses; `FieldOfNorms.inclusion`: the ring homomorphism.
- `FieldOfNorms.map τ`, for `τ : L →ₐ[K] M` with `M` finite separable over `τ(L)`: `inclusion` composed with `mapEquiv` onto the image.
- `FiniteIntermediateField.pullbackEquiv`, `tensorAddEquiv`: transport of pullbacks and of the tensor product along a commuting square of isomorphisms; they give `isGoodFiniteLayer_map_iff`.

## Results

- Coordinates: `coe_coord_mapEquiv`, `coord_inclusion`, `coord_inclusion_of_le`, `coe_coord_map`.
- Uniqueness: `inclusion_unique`, `map_unique` (the coordinates at good fields determine the map).
- Valuation: `valuation_mapEquiv` (preserved); `exists_valuation_inclusion_eq_pow`, `exists_valuation_map_eq_pow` (raised to a fixed power `e > 0`); hence `uniformContinuous_mapEquiv`, `uniformContinuous_inclusion`, `uniformContinuous_map`.
- Functor laws: `mapEquiv_refl`, `mapEquiv_trans`, `inclusion_self`, `inclusion_inclusion`, `map_id`, `map_map`.
- Comparisons: `map_algEquiv` (`map` of an isomorphism is `mapEquiv`), `map_toAlgHom` (`map` of an inclusion is `inclusion`), `mapEquiv_inclusion`, `mapEquiv_map` (naturality for commuting squares).
- Finite fields: `spectral_normalizedValuation_algHom` (an embedding raises the normalized valuation to the power of its ramification index).

## Proofs

Additivity of `mapEquiv` and of `inclusion` comes from the description of the sum as a limit of norms of sums of coordinates (`FieldOfNorms.tendsto_normSumNet_add`). Norm compatibility on good pairs is `goodFinitePair_norm`; good fields are cofinal (`exists_goodFiniteLayer_ge`), and identities are checked on a cofinal family by `FieldOfNorms.ext_cofinal`. Composition uses fields good for the whole tower (`exists_goodFiniteLayer_tower_ge`).

## To watch for

- `inclusion` and `map` are for finite separable steps only; an arbitrary embedding of APF extensions is not covered.
- The formula for `inclusion` holds at good fields; elsewhere a norm from a good field is taken.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §3.1; Remark 3.2.4.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Functor/Map.lean` (SHA-256 of the source file `c557f359f0be7d6737d5114f7c3c0cf30b3ee784ea9c8f81b7364c61ebe20386`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
