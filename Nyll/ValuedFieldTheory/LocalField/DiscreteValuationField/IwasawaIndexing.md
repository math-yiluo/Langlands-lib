# Reindexing the Iwasawa product of copies of ℤ_p

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.IwasawaIndexing`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In equal characteristic, the first principal units are described as a product of copies of `ℤ_p` indexed by pairs: a positive degree prime to `p` and a basis vector of the residue field. This file shows that this index set is countably infinite, so that the product is `ℤ_p^ℕ`.

## Main definitions and results

- `IwasawaDegree p`: positive integers prime to `p`. `IwasawaIndex p f = IwasawaDegree p × Fin f`.
- `iwasawaDegreeEmbedding`: the injection `k ↦ 1 + pk` of `ℕ`, for `p > 0`.
- `infinite_iwasawaIndex`: the index set is infinite when `p > 0` and `f > 0`.
- `chosenIwasawaIndexEquivNat`: a bijection of the index set with `ℕ`.
- `iwasawaPadicIntProductContinuousAddEquivNat`: for `p` prime and `f > 0`, an isomorphism of topological additive groups `(IwasawaIndex p f → ℤ_p) ≃ₜ+ (ℕ → ℤ_p)`, for the product topologies.

## Points to watch

- The bijection with `ℕ` comes from `Classical.choice` of a `Denumerable` structure, so neither it nor the resulting isomorphism is canonical.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/IwasawaIndexing.lean`: the Lean file is the source byte for byte (SHA-256 `1f0ad1f10da557a7b293ef535f382c4f2afbfc3ceb52f220a3baef0c2e33ecfa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
