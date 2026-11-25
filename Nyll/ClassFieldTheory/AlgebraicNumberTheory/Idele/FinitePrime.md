# The idele of a finite prime

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K` and a finite place `v`, the file defines an idele that has local order one at `v` and is `1` at every other place. It then computes the fractional ideal and the ideal class attached to it.

## Main declarations

- `IdeleGroup.finitePrimeIdele v`: the one-place idele at `v` whose component is `FiniteIdeleGroup.chosenLocalOrderSection v 1`, a chosen element of `K_vˣ` of local order one.
- `fractionalIdeal_finitePrimeIdele`: its fractional ideal is the prime ideal of `v` (`FractionalIdealGroup.prime v`). The exponents are compared place by place: `1` at `v` and `0` elsewhere.
- `idealClass_finitePrimeIdele`: its ideal class is the class of that prime.

## Points to watch

- The idele depends on the library's choice `chosenLocalOrderSection`, an element of order one at `v`; it is not canonical, but its fractional ideal and ideal class are.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/FinitePrime.lean`: the Lean file is the source byte for byte (SHA-256 `54e26d6aa61e414bdd9609c6418da5fb5a0dfd0bb3b289204a59ec4cf05e4a33`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
