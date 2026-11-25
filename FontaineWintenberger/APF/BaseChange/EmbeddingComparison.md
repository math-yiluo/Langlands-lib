# Ramification numbers of embeddings of nonnormal finite extensions

Module `FontaineWintenberger.APF.BaseChange.EmbeddingComparison`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field (`IsPerfectResidueLocalField K`), `Ω/K` a finite Galois extension with group `G`, and `E ≤ F` intermediate fields, not assumed normal. For two `K`-embeddings `α, β` of a finite extension, the library has an order `embeddingRamificationOrder K α β`, the infimum of the valuations of `α(x) - β(x)` over integers `x` divided by a ramification index, and a number `embeddingRamificationNumber K α β`, the order minus one, in the extended reals. This file computes them for restrictions `s|E` of elements `s` of `G` and compares `s|F` with `s|E`.

## Main results

- Ultrametric inequality for three ring maps into a discrete valuation ring, with equality when two orders differ: `min_integralEmbeddingOrder_le`, `integralEmbeddingOrder_eq_min_of_ne`, `embeddingNumber_eq_of_lt_pair`.
- A lemma of Tate for an arbitrary algebra map `f : A → B`: if `y` generates `A` and `x` generates `B` over `R`, then `f(y) - y` is associated to the value at `x` of the image under `f` of the minimal polynomial of `x` over `A` (`associated_generator_pair_sub_eval_map_minpoly`).
- Coset sums: the unnormalized order of `(s|E, id)` is the sum over `h` in the fixing subgroup `H` of `E` of `ramificationOrder (s·h)` (`embeddingIntegralOrder_fixedField_eq_sum`, `embeddingOrder_intermediate_eq_sum_div`).
- `exists_embeddingNumber_intermediate_eq_herbrand`: if `s` does not fix `E`, some `r` with `r|E = s|E` has maximal finite order in its coset, and the number of `s|E` is the Herbrand function of `H` at `ramificationOrder r - 1`.
- `embeddingNumber_restriction_le_apfPsi`: if `s` does not fix `E`, the number of `s|F` is at most `ψ(F/E) = apfPsi E F` of the number of `s|E`; `apfPsi_extendScalars_eq_fixing_herbrand` writes `ψ(F/E)` through Herbrand functions of the two fixing subgroups.
- `apfRamificationBound_le_embeddingNumber`: `i(F/K)` is at most the number of `s|F`, for every `s`. `apfRelativeBound_le_pairNumber`: if `s|E = t|E`, then `i(F/E)` is at most the number of `(s|F, t|F)`.
- `embeddingNumber_rebase`: for `s` fixing `E`, the number of `s|F` is the same over `K` and over `E`.
- When `F/E` is totally ramified: `sum_embedding_extension_order_of_totallyRamified` (an averaging identity for the orders of the `(s·d)|F`, `d` fixing `E`), and `embeddingNumber_eq_restriction_of_lt_relativeBound`: if the number of `s|E` is below `i(F/E)`, then `s|F` has the same number as `s|E`.

## Proofs

The coset sum comes from Tate's lemma and the factorization of a minimal polynomial over `H`.

## What to watch for

- Total ramification of `F/E` is the hypothesis `htotal`: the ramification index of the inclusion equals the degree.
- Statements involving `ψ(F/E)` or `i(F/E)` introduce the valued structure on `E` by `letI`.
- `ramificationOrder`, `herbrandFunction` and the embedding orders are the library's notions, attached to `spectralIntegerRing`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/BaseChange/EmbeddingComparison.lean` (SHA-256 of the source file `759e57152a552dc281ecc3dce7c4beed88c2831054f61c72d1fdf790ec96ee39`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
