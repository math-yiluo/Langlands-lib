# Local components determine relative adeles and ideles

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.LocalComponents`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields, and let `RelativeAdeleRing K L` be the relative adele ring 𝔸_K ⊗_K L. Every relative adele has a component in K_w ⊗_K L at each infinite place w of K, and in `w.adicCompletion K ⊗[K] L` at each finite place. This file shows that these components together determine the adele. It deduces an injective group homomorphism from relative ideles to the unrestricted product of the local tensor unit groups.

## Results

- `relativeAdeleFiniteComponent_basis_repr` and `relativeAdeleInfiniteComponent_basis_repr`: in the basis of K_w ⊗_K L induced by the fixed K-basis of L, the i-th coordinate of the component of z at w is the value at w of the i-th adelic coefficient `relativeAdeleCoefficient z i`.
- `relativeAdele_ext_of_components`: two relative adeles with the same component at every infinite and every finite place are equal.
- `RelativeLocalTensorFamily`: the unrestricted product of (K_w ⊗_K L)ˣ over all infinite places, paired with the same product over all finite places.
- `relativeIdeleLocalComponents`: the group homomorphism sending a relative idele (an element of `RelativeIdeleGroup K L`, a unit of the relative adele ring) to the family of its local components. Two simp lemmas give its infinite and finite parts.
- `relativeIdeleLocalComponents_injective`: this homomorphism is injective.

## Proofs

The coordinate formulas come from writing each component as a sum of the coefficients tensored with the basis vectors. Equality of all components then gives equality of all coefficients. Since the coefficient map `relativeAdeleCoefficientLinearEquiv` is a linear isomorphism, the adeles are equal.

## Points to watch

- Only injectivity is proved here. The module comment says that the image, a restricted product of local units, is described in other files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/LocalComponents.lean`: the Lean file is the source byte for byte (SHA-256 `6f8c5273214072f6dd0db1a7099a7304d620a3c643ea214c2d2e1228e12a1d55`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
