# Upper ramification groups as inverse limits; the absolute case

Module `FontaineWintenberger.Ramification.Infinite.Limit`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field in the library's sense, with perfect residue field, and `Ω/K` a field extension. For `u ≥ −1` the file identifies the infinite upper ramification group `upperRamificationGroupInfinite K Ω u` with the inverse limit of the upper ramification groups of the finite Galois subextensions, and specializes to the separable closure.

## Definitions

- `finiteUpperRamificationGroupMap K Ω f u hu`: for finite Galois subextensions `B ≤ A`, the continuous homomorphism from the upper group of `A/K` at `u` to that of `B/K`, induced by restriction.
- `finiteUpperRamificationGroupFunctor K Ω u hu`: the functor from `(FiniteGaloisIntermediateField K Ω)ᵒᵖ` to `ProfiniteGrp` formed by these groups and maps.
- `upperRamificationToLimit`: the homomorphism from `upperRamificationGroupInfinite K Ω u` to `ProfiniteGrp.limit` of that functor, given by restrictions.
- `upperRamificationLimitForget`: the map from this limit to the limit of all finite Galois groups, forgetting membership in the upper groups.
- `upperRamificationEquivToLimit` (for `Ω/K` Galois): the isomorphism of topological groups between `upperRamificationGroupInfinite K Ω u` and the limit.
- `absoluteUpperRamificationGroup K u`: an abbreviation for `upperRamificationGroupInfinite K (SeparableClosure K) u`.
- `absoluteUpperImageEquivToLimit`: for a Galois intermediate field `L` of the separable closure, the isomorphism between the image of the absolute upper group in `L ≃ₐ[K] L` and the limit of the finite upper groups of `L`.

## Results

- `finiteUpperRamificationGroupMap_id`, `finiteUpperRamificationGroupMap_comp`: functoriality.
- `continuous_upperRamificationToLimit`, `upperRamificationToLimit_bijective` (the latter for `Ω/K` Galois).
- `upperRamificationEquivToLimit_apply_val`, `absoluteUpperImageEquivToLimit_apply_val`: the coordinate at `E` of these isomorphisms is the restriction to `E`.
- `absolute_map_upperRamificationGroup`: the image of the absolute upper group in `E ≃ₐ[K] E`, for `E` finite Galois, is the upper group of `E/K`.
- `absolute_restrict_map_upperRamificationGroupInfinite`: its image in `L ≃ₐ[K] L`, for `L/K` Galois inside the separable closure, is `upperRamificationGroupInfinite K L u`.

## Proofs

That the transition maps land in the upper groups is the compatibility of upper numbering with quotients (`finGaloisGroupMap_map_upperRamificationGroup`). Bijectivity is deduced from Mathlib's isomorphism `InfiniteGalois.mulEquivToLimit` between `Gal(Ω/K)` and the limit of the finite Galois groups; the inverse is continuous because the source is compact and the target Hausdorff. The absolute statements are the surjectivity results of the two preceding files on infinite extensions.

## What to watch for

- The limit is Mathlib's `ProfiniteGrp.limit`; finite upper groups carry the discrete topology.
- The absolute group lives in the automorphism group of Mathlib's `SeparableClosure K`. The definition `absoluteUpperRamificationGroup` itself does not need the residue field to be perfect; the results do.
- All statements carry the hypothesis `−1 ≤ u`, which is an argument of the functor.
- `absoluteUpperImageEquivToLimit` is defined by rewriting along an equality of subgroups.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Infinite/Limit.lean` (SHA-256 of the source file `8c281d019c37e6c789883f885b67964fb6c5ba44e76524c0dd287091802f88b6`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
