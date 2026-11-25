# Ramification orders of pairs of embeddings

Module `FontaineWintenberger.Ramification.Embedding.Basic`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For two `K`-embeddings `σ, τ : E → N` of finite separable extensions of a local field `K`, the file defines an order measuring how close `σ` and `τ` are on integers, normalizes it to be independent of `N`, and extends it to embeddings into the separable closure. Subtracting one gives Wintenberger's ramification numbers.

## Definitions

- `integralEmbeddingOrder f g : ℕ∞`, for ring homomorphisms `f, g : S →+* T` into a discrete valuation ring: the infimum over `x` of `addVal T (f x − g x)`.

For `K` with `IsPerfectResidueLocalField K`, and `E`, `N` finite separable over `K`, with rings of integers `spectralIntegerRing`:

- `embeddingRamificationIdx K σ : ℕ`: the ramification index of the integer rings along `σ`.
- `embeddingIntegralOrder K σ τ : ℕ∞`: `integralEmbeddingOrder` of the maps induced on integer rings.
- `embeddingRamificationOrder K σ τ : ℝ≥0∞`: the integral order divided by `embeddingRamificationIdx K σ`.
- `embeddingPairField K σ τ`: for embeddings into `SeparableClosure K`, the compositum of the two images.
- `closureEmbeddingOrder K σ τ`: the normalized order computed in `embeddingPairField`.
- `embeddingRamificationNumber`, `closureEmbeddingNumber`: the corresponding orders minus `1`, in `EReal`.

## Results

- `integralEmbeddingOrder_eq_generator`: for algebra maps, the infimum is attained at any `x` with `Algebra.adjoin R {x} = ⊤`.
- `integralEmbeddingOrder_eq_uniformizer`: if `S` is a discrete valuation ring with perfect residue field of characteristic `p`, `p` lies in the maximal ideal of `T`, `g` is local and `f ≡ g` modulo the maximal ideal, then the order is attained at every uniformizer.
- `embeddingRamificationIdx_comp`, `embeddingRamificationIdx_eq`: the index is multiplicative and is the same for all embeddings `E → N`.
- The orders are symmetric, equal `⊤` exactly when `σ = τ`, and vanish when the residue maps differ (`one_le_embeddingIntegralOrder_iff`).
- `embeddingIntegralOrder_comp`, `embeddingRamificationOrder_comp`: composing with `u : N → M` multiplies the integral order by the index of `u` and leaves the normalized order unchanged.
- `closureEmbeddingOrder_eq_finite`, `closureEmbeddingOrder_comp`: the order in the closure agrees with the normalized order in any finite ambient field.
- `embeddingRamificationOrder_aut`, `closureEmbeddingOrder_aut`: for an automorphism `s` of `E`, the order of `(s, id)` is `ramificationOrder s`.
- `embeddingRamificationNumber_nonneg`: the number is `≥ 0` when the residue maps agree; it is `−1` when they differ and `⊤` when `σ = τ`.

## What to watch for

- All notions here are the library's own; the "number" is the order minus one.
- `closureEmbeddingOrder` puts no valuation on the separable closure; it is computed in a finite compositum.
- Neither normality of `E` nor finiteness of the residue field is assumed.

## References

Serre, *Local Fields*, Chapter IV; Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.1.1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Embedding/Basic.lean` (SHA-256 of the source file `a03cbce299223b8798b52160a06c4d4d953e0df1e488ac3ff0d61612a6a198df`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
