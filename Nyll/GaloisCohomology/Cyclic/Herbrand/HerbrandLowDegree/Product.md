# Low-degree Tate groups of dependent products

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Product`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite group `G` and a family `A i`, `i : ι`, of multiplicative `G`-modules, the file shows that the library's groups `HerbrandH0` and `HerbrandHMinusOne` of the product `∀ i, A i`, with the componentwise action, are the products of those of the factors. This is the product step for low-degree Herbrand quotients.

## Main definitions and results

- `piMulDistribMulAction G A`: the componentwise action on `∀ i, A i`.
- `piSubgroup ι A N`: the pointwise product of subgroups `N i ≤ A i`; the componentwise quotient map `piQuotientMap` (`ker_piQuotientMap`, `piQuotientMap_surjective`) and `piQuotientEquiv : (∀ i, A i) ⧸ piSubgroup ι A N ≃* ∀ i, A i ⧸ N i`.
- `fixedPiEquiv`, `normKernelPiEquiv`: fixed points and norm kernels of the product are the products of those of the factors.
- `herbrandH0PiEquiv : HerbrandH0 G (∀ i, A i) ≃* ∀ i, HerbrandH0 G (A i)`.
- `herbrandHMinusOnePiEquiv σ : HerbrandHMinusOne G (∀ i, A i) σ ≃* ∀ i, HerbrandHMinusOne G (A i) σ`.

## Proofs

Since `G` is finite, the norm and `σ − 1` of the product are computed componentwise, so the norm image and the augmentation image of the product are the products of those of the factors (preimages are chosen componentwise with `choose`). The equivalences then come from `quotientMulEquivOfSplit` followed by `piQuotientEquiv`.

## Points to watch

- The index type `ι` is arbitrary, possibly infinite, and the product is the full product, not a restricted one.
- All `A i` lie in one universe.
- The action on the product is the file's reducible definition `piMulDistribMulAction`, installed as a local instance in the section of the main results.
- `σ` is arbitrary; no cyclicity is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Product.lean`: the Lean file is the source byte for byte (SHA-256 `9c5b0501a3a4d0a0182a39e332c4468a70e09bd6b5fb5a7bb08625211f7ac4b1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
