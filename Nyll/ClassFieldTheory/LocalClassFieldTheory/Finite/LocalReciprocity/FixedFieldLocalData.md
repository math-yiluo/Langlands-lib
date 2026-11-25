# Local valuation and residue degree on finite fixed fields

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldLocalData`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a nonarchimedean local field. The local class formation attaches to each finite abstract field `H` (a closed subgroup of finite index in `Gal(SeparableClosure K / K)`) a valuation and residue degrees computed inside the separable closure of `K`. This file shows that they agree with the intrinsic data of the concrete fixed field of `H`, given the spectral norm extending the topology of `K`; the residue-degree comparison extends to any finite separable extension of `K` embedded into `SeparableClosure K`.

## Main results

- `finiteFixedField K H`: the fixed field of `H` in `SeparableClosure K`.
- `localHenselianValuation_valuationAt_abstractFixedField`: for a unit `x` of the fixed field, the `ZHat`-valued valuation of `localHenselianValuation K` at `H` equals the image in `ZHat` of the normalized integer valuation of `x`.
- `localSeparableValuationSubring_eq_comap_finiteExtensionEquiv`: for a finite separable extension `F/K` of local fields, an embedding `i : F →ₐ[K] SeparableClosure K` and any `F`-isomorphism `e : SeparableClosure F ≃ SeparableClosure K`, the chosen valuation ring of `SeparableClosure F` is the pullback along `e` of that of `SeparableClosure K`. Consequences: the whole Galois group of `F` stabilizes the ambient valuation ring, and the decomposition residue field of `F` at that ring is finite.
- `localSeparableValuationSubring_eq_comap_abstractFixedFieldEquiv`: the same comparison for the fixed field of `H`.
- `localResidueDegree_semilinear_conjugation`: `localResidueDegree` is invariant under a semilinear isomorphism of local fields and separable closures matching the chosen valuation rings.
- `localResidueDegree_eq_normalizedDegree_abstractFixedFieldEquiv`: for `σ` in the Galois group of the fixed field, `localResidueDegree` of `σ` equals the normalized degree of `localResidueDatum K` at the element of `H` corresponding to `σ` through `e`.
- `localResidueDegree_eq_normalizedDegree_finiteExtensionEquiv`: the same for an arbitrary finite separable `F`, with `H` the fixing subgroup of the image of `i`; `F` need not be a fixed-field subtype.

## Proofs

The valuation comparison uses that the norm from the fixed field to `K` multiplies valuations by the residue degree `f`, identifies `f` with the residue degree of the datum, and divides by `f` in `ZHat`. The degree comparisons conjugate residue actions through isomorphisms of residue fields and use the invariance of `residueAbsoluteDegreeIn` under semilinear conjugation.

## Points to watch

- The fixed field carries no local field structure of its own: the statements install, by `letI`, the spectral norm, valuative relation and local field instance coming from `K`, and hold for that structure.
- For an arbitrary `F`, the given valuations must be compatible: `Valuation.HasExtension (valuation K) (valuation F)` is a hypothesis.
- `localResidueDegree`, `normalizedDegree` and `localHenselianValuation` are the library's own notions from the class formation set-up.
- The fields `K` and `F` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean`: the Lean file is the source byte for byte (SHA-256 `3ed2da20eba7d80d347fcd89b1029192120dc9bbc8a68f9badb4e291d9a83839`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
