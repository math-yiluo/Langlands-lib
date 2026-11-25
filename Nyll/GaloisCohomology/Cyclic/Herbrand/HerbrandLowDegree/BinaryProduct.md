# Tate groups in degrees 0 and −1 of a product of two modules

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.BinaryProduct`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite group `G` and two multiplicative `G`-modules `A` and `B`, the file shows that the library's groups `HerbrandH0` and `HerbrandHMinusOne` of `A × B` are the products of those of `A` and `B`, and that the Herbrand quotient is multiplicative on binary products. Its comment says it serves to join the unrestricted and the integral parts of a supported idele group.

## Main definitions and results

- `BinaryCoefficientFamily A B : Bool → Type`, sending `false` to `A` and `true` to `B`, with componentwise group and action structures (`binaryCoefficientFamilyCommGroup`, `binaryCoefficientFamilyAction`, used as local instances), and the equivariant reindexing `prodEquivBinaryCoefficientFamily : A × B ≃* ∀ i, BinaryCoefficientFamily A B i` (equivariance: `prodEquivBinaryCoefficientFamily_smul`).
- `herbrandH0ProdEquiv : HerbrandH0 G (A × B) ≃* HerbrandH0 G A × HerbrandH0 G B`, and `herbrandHMinusOneProdEquiv σ` in degree −1.
- `herbrandH0ProdFinite`, `herbrandHMinusOneProdFinite`: finiteness of the groups of `A` and of `B` gives finiteness for `A × B`.
- `herbrandH0Prod_card`, `herbrandHMinusOneProd_card`: the orders multiply.
- `herbrandQuotient_prod`: if the four groups of `A` and `B` are finite, the `herbrandQuotient` of `A × B` is the product of those of `A` and `B`.

## Proofs

`A × B` is reindexed as a dependent product over `Bool`. The equivalence induced by an equivariant isomorphism (`herbrandH0EquivariantMulEquiv`) and the dependent-product equivalence (`herbrandH0PiEquiv`, and their degree −1 versions) are composed with the reindexing back to a binary product. The statement on quotients follows from the formulas for the orders.

## Points to watch

- `A` and `B` must lie in the same universe.
- The action on `A × B` is the componentwise one.
- No generator hypothesis appears: `σ` is arbitrary and `G` need not be cyclic.
- In `herbrandH0Prod_card`, `herbrandHMinusOneProd_card` and `herbrandQuotient_prod`, the finiteness instances for `A × B` are bound inside the statement, from `herbrandH0ProdFinite` and `herbrandHMinusOneProdFinite`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/BinaryProduct.lean`: the Lean file is the source byte for byte (SHA-256 `9e32142293d1bd3ab6aa28c4e90fc93bd6457c7f5704a66b477413488d71af4e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
