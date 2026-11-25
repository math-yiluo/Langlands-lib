# Coordinates of relative adeles

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.Coordinates`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension L/K of number fields, the relative adele ring `RelativeAdeleRing K L` (the adeles 𝔸_K ⊗_K L) is free over 𝔸_K on the chosen K-basis of L. This file supplies the inverse of the coordinate map: from a family of base adeles indexed by the basis it assembles a relative adele.

- `relativeAdeleCoefficientLinearEquiv`: the 𝔸_K-linear isomorphism from relative adeles to families of base adeles, the coordinates in the chosen basis; its components are `relativeAdeleCoefficient`.
- `relativeAdeleOfCoefficients`: the inverse map, with `relativeAdeleCoefficient_ofCoefficients` and `relativeAdeleOfCoefficients_coefficients` saying the two are mutually inverse.
- `relativeAdeleOfCoefficients_finiteComponent`, `…_infiniteComponent`: at a finite place w, or an infinite place w, of K, the component of the assembled adele is Σᵢ aᵢ,w ⊗ eᵢ, with eᵢ the chosen basis of L.
- `relativeIdeleOfCoefficientFamilies`: from two coefficient families a, b whose assembled adeles multiply to 1 (hypothesis `hab`), the relative idele with value the assembly of a.

The coordinates depend on the basis `relativeExtensionBasis` fixed in the imported support file. Invertibility of an assembled adele is not deduced from its components: it is the hypothesis `hab`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/Coordinates.lean`: the Lean file is the source byte for byte (SHA-256 `8f8e5b39f3a50fbf365977e49db66a7b55277016d3f7f9d3731783318c8696c4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
