# Realizing a finite Galois extension inside the separable closure

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

To apply abstract class-formation theory to a finite Galois extension `L / K`, the library embeds `L` into `SeparableClosure K`. The closed subgroup fixing the image is the abstract field attached to `L`. This file shows that the corresponding fixed coefficient group is `Lˣ`, that the abstract extension quotient is `Gal(L / K)`, and that the index is `[L : K]`. Everything is done twice: for an explicit `K`-embedding `i : L → SeparableClosure K`, and for the chosen embedding `AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L`.

## For an explicit embedding

- `finiteGaloisFieldRangeOfEmbedding K L i`: the image `i(L)` as an intermediate field, with `finiteGaloisFieldRangeEquivOfEmbedding : L ≃ₐ[K] i(L)` and instances saying that `i(L)` is finite and Galois over `K`.
- `finiteGaloisClosedFixingSubgroupOfEmbedding`: the closed subgroup of `Gal(SeparableClosure K / K)` fixing `i(L)`; the instance `finiteGaloisExtensionSubgroupOfEmbedding_normal` makes it normal in the base subgroup.
- `finiteGaloisUnitsEquivAbstractFixedOfEmbedding`: `Lˣ` is isomorphic to the units of the separable closure fixed by this subgroup, by `x ↦ i(x)` (`finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe`).
- `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding`: the abstract extension quotient is isomorphic to `Gal(L / K)`.
- `finiteGaloisExtensionSubgroupOfEmbedding_index_eq_finrank`: the index of the subgroup is `[L : K]`.

## For the chosen embedding

`finiteGaloisFieldRange`, `finiteGaloisFieldRangeEquiv`, `finiteGaloisClosedFixingSubgroup`, `finiteGaloisExtensionSubgroup_normal`, `finiteGaloisUnitsEquivAbstractFixed`, `finiteGaloisAbstractQuotientEquivGaloisGroup` and `finiteGaloisExtensionSubgroup_index_eq_finrank` specialize the above to the chosen embedding, with matching instances.

## Proof

The quotient isomorphism is `baseFixingExtensionQuotientEquivGaloisGroup` for the field `i(L)`, transported to `L` along `L ≃ₐ[K] i(L)`. The index is the cardinality of the quotient, hence of `Gal(L / K)`, which is `[L : K]` by `IsGalois.card_aut_eq_finrank`.

## Points to watch

- No perfectness hypothesis is made, so the results apply in equal characteristic, for instance to finite extensions of `𝔽_q((t))`; in fact `K` may be any field, and `K`, `L` may lie in different universes.
- The chosen-embedding versions depend on a choice. The docstring explains that the explicit-embedding versions are kept so that independence of the choice can be argued.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean`: the Lean file is the source byte for byte (SHA-256 `9e582854a79e354332720c763351cd96a3252edcd44a9ad5c7ff0c065e4f1627`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
