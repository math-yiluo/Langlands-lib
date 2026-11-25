# Splitting supported relative ideles at a finite set of places

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Reassociation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields and `S` a finite set of finite places of `K` (`Finset (HeightOneSpectrum (𝓞 K))`). The relative ideles supported at `S` (built from the local tensor decompositions `L ⊗ K_v`) split as a product of the unrestricted local factors, at the infinite places and at the places of `S`, and the integral unit factors at the finite places outside `S`. The file states this splitting, shows it commutes with the Galois action, and transports the groups `HerbrandH0` and `HerbrandHMinusOne` along it.

## Main declarations

- `RelativeOutsideSPlaceFactors S`: the product, over finite places `v ∉ S`, of the integral unit subgroups `relativeLocalTensorDecompositionIntegralUnitSubgroup v`; `relativeOutsideSPlaceFactorsAction` is the componentwise action of `L ≃ₐ[K] L`, and `relativeUnrestrictedProdOutsideAction` the action on `RelativeUnrestrictedSPlaceFactors S × RelativeOutsideSPlaceFactors S`.
- `relativeIdeleSPlaceFactorsEquivUnrestrictedProdOutside`: a multiplicative equivalence from the factor model `RelativeIdeleSPlaceFactors S` to this product, which regroups the components; `_smul` states that it is Galois equivariant.
- `relativeIdeleSupportedEquivUnrestrictedProdOutside`: the composite with `relativeIdeleSupportedEquivSPlaceFactors`, an equivalence from the supported subgroup `relativeIdeleLocalTensorDecompositionSupportedSubgroup S` to the product; `_smul` gives equivariance, checked component by component with `RelativeIdeleGroup.infiniteComponent_smul` and `finiteComponent_smul`.
- `relativeIdeleSupportedHerbrandH0EquivUnrestrictedProdOutside` and `relativeIdeleSupportedHerbrandHMinusOneEquivUnrestrictedProdOutside`: the induced isomorphisms of `HerbrandH0` and `HerbrandHMinusOne`, which the file calls Tate cohomology in degrees 0 and −1. They are obtained from `herbrandH0EquivariantMulEquiv` and `herbrandHMinusOneEquivariantMulEquiv`.

## Points to watch

- `S` contains only finite places; the infinite places always count among the unrestricted factors.
- `HerbrandHMinusOne` is the library's own group and is taken with respect to a chosen element `σ` of the Galois group, so the second isomorphism is stated for each `σ`; no hypothesis that `σ` generates the Galois group is made.
- The actions are given as `@[reducible]` defs and supplied by `let`, not as instances.
- `K` and `L` are taken in `Type`, the lowest universe.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/Reassociation.lean`: the Lean file is the source byte for byte (SHA-256 `d550e6b2cdad1acc23d583cbb643b0aa49aab70137b42b5f52a919434f14d2dd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
