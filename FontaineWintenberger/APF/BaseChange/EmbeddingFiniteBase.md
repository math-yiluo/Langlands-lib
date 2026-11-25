# Ramification numbers of embeddings over an abstract finite base

Module `FontaineWintenberger.APF.BaseChange.EmbeddingFiniteBase`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field (`IsPerfectResidueLocalField K`). The file extends the comparison of ramification numbers of embeddings, proved for intermediate fields of a finite Galois extension, to a finite base `M/K` given as an abstract complete normed field with `NormedAlgebra K M`, and to finite separable extensions `F` given as types.

## Results

- `embeddingNumber_restrictScalars_of_normedAlgebra`: for finite separable `F` and `Ω` over `K`, both over `M`, and `M`-embeddings `σ, τ : F → Ω`, the number `embeddingRamificationNumber` is the same whether computed over `K` or over `M`.
- `exists_aut_comp_intermediate`: an embedding of an intermediate field of a normal extension `Ω/K` into `Ω` is the restriction of an automorphism of `Ω`.
- `apfRamificationBound_le_embeddingPairNumber`: for `Ω/K` finite Galois, `F/K` finite separable and any two `K`-embeddings `σ, τ : F → Ω`, `apfRamificationBound K F ≤ embeddingRamificationNumber K σ τ`.
- `apfRelativeBound_le_embeddingPairNumber_of_normedAlgebra`: for `M`-embeddings `σ, τ : F → Ω`, `apfRamificationBound M F` is at most their number computed over `K`.
- `apfRelativeBound_le_pairNumber_of_normedAlgebra`: for an embedding `i : F → Ω` and `s, t` in `Gal(Ω/K)` such that `s ∘ i` and `t ∘ i` agree on `M`, `apfRamificationBound M F` is at most the number of the pair `(s ∘ i, t ∘ i)`.
- `embeddingNumber_eq_restriction_of_lt_bound`: let `E ≤ D` be intermediate fields of `Ω`, `e : F ≃ D` a `K`-isomorphism under which the image of `M` lies in `E`, and suppose `D/E` totally ramified. If `s` in `Gal(Ω/K)` does not fix `E` and the number of `s|E` is smaller than `apfRamificationBound M F`, then `s|D` and `s|E` have the same number.

## Proofs

Restriction of scalars is handled by identifying the spectral integer rings over `K` and over `M` as the same unit balls and transporting the local ramification index. The last result follows the argument of the intermediate-field version: an average over the fixing subgroup of `E` under total ramification, and the equality case of the ultrametric inequality.

## What to watch for

- Total ramification of `D/E` is the hypothesis `htotal`: `embeddingRamificationIdx K` of the inclusion equals the degree of `D` over `E`.
- In the statements over `M`, the perfect-residue structure on `M`, the separability and the finiteness over `M` are introduced by `letI` inside the statement; in two of them the `M`-algebra structure on `Ω` is built in the proof from the given embeddings.
- `embeddingRamificationNumber` and `embeddingRamificationIdx` are the library's notions, defined in its ramification modules.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/BaseChange/EmbeddingFiniteBase.lean` (SHA-256 of the source file `2a4c9022f9ab3c196604d13ec9f9b07bbf687ff289f6f7f02d5cd66708bcc588`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
