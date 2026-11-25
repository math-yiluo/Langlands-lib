# Relative adeles and ideles as restricted products of local tensor factors

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedProduct`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields, with the fixed K-basis of L given by `relativeExtensionBasis`. This file describes 𝔸_K ⊗_K L place by place. A family (x_w) with x_w ∈ K_w ⊗_K L at every place comes from a relative adele exactly when each basis coordinate of x_w is integral at almost every finite place. A family of units comes from a relative idele exactly when this holds for the family and for its pointwise inverse.

## Definitions

- `RelativeLocalAdeleData`: a structure. It has components in K_w ⊗_K L at the infinite places and in `w.adicCompletion K ⊗[K] L` at the finite places. Each basis coordinate of the finite components must lie in the integers of K_w for all but finitely many w.
- `relativeLocalAdeleCoefficient a i`: the adele of K formed by the i-th coordinates of the components. `relativeAdeleOfLocalData` assembles the family into a relative adele, and `relativeAdeleToLocalData` extracts the components of a relative adele.
- `RelativeLocalIdeleData`: the same with local units, and with the integrality condition imposed both on the family and on its pointwise inverse. `RelativeLocalIdeleData.value` and `.inverse` forget invertibility.
- `relativeIdeleToLocalData` and `relativeIdeleOfLocalData`: the two directions for ideles. The second builds a unit of the relative adele ring from the two adeles assembled from the family and from its inverse.

## Results

- `relativeAdeleOfLocalData_infiniteComponent` and `..._finiteComponent`: the assembled adele has the prescribed local components. `relativeAdeleOfLocalData_toLocalData` and `relativeAdeleToLocalData_ofLocalData` say the two constructions are mutually inverse.
- `relativeAdeleEquivLocalData`: a bijection between `RelativeAdeleRing K L` and `RelativeLocalAdeleData`.
- The corresponding statements for ideles, leading to `relativeIdeleEquivLocalData`: a bijection between `RelativeIdeleGroup K L` and `RelativeLocalIdeleData`.
- `relativeLocalIdeleDataGroup` (instance) and `relativeIdeleMulEquivLocalData`: the group structure transported along this bijection, which becomes a group isomorphism. `RelativeLocalIdeleData.infinite_mul` and `.finite_mul` show that the transported product is computed coordinatewise.

## Proofs

Everything reduces to the coordinate formulas and to the injectivity of the component maps, both from `LocalComponents`. A relative adele is determined by its basis coefficients, which are adeles of K. The idele case applies the adele case to the family and to its inverse.

## Points to watch

- Restrictedness is defined through the fixed K-basis of L, not through valuation rings of completions of L. The module comment notes that the comparison with products of local integer rings is made later and independently.
- The bijection for adeles is only a bijection of sets. No ring structure or topology is put on `RelativeLocalAdeleData`.
- The group structure on `RelativeLocalIdeleData` is transported. That it is coordinatewise is a theorem.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/RestrictedProduct.lean`: the Lean file is the source byte for byte (SHA-256 `171fd29c533f4934fa83d7da71dff35a75a7b5ceef5de47ce154a04dc2e71cc1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
