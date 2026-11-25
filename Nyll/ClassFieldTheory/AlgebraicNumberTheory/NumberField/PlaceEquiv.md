# Places under an isomorphism of number fields

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.PlaceEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A ring isomorphism `e : F ≃+* G` of fields induces bijections between their places. This file records these bijections, used to reindex products over places.

## Main definitions

- `ClassFieldTheory.finitePlaceEquivOfRingEquiv e`: for number fields `F` and `G`, the bijection between the height-one primes of `𝓞 F` and of `𝓞 G` induced by the isomorphism of rings of integers that `e` restricts to.
- `ClassFieldTheory.infinitePlaceEquivOfRingEquiv e`: the bijection between infinite places sending a place `w` of `F` to its pullback along `e⁻¹`, with inverse the pullback along `e`.

## Points to watch

- Only the bijections are defined; the file states no compatibility with absolute values, completions or ramification.
- The infinite-place bijection is stated for arbitrary fields, without the number-field hypothesis.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/NumberField/PlaceEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `79ea4e47686928ee0cb15cb9173ddddf9204e24c150de53256d7342a03c02c08`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
