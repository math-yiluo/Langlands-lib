# Splitting of primes in the small Hilbert class field

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertSplitting`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, the small Hilbert class field has reciprocity quotient `C_K / N` (with `N` its norm subgroup in the idele class group) isomorphic to the ideal class group. This file uses that isomorphism to describe the Frobenius class of a finite prime and the primes that split completely.

- `smallHilbertFrobeniusClass v`: for a height-one prime `v` of `𝓞 K`, the element of `IdeleClassGroup K ⧸ smallHilbertClassFieldNormSubgroup` corresponding to the ideal class of `v` under the inverse of `smallHilbertClassFieldQuotientEquivClassGroup`.
- `SplitsCompletelyInSmallHilbertClassField v`: defined as `smallHilbertFrobeniusClass v = 1`.
- `splitsCompletelyInSmallHilbertClassField_iff_principal`: this holds if and only if the fractional ideal of `v` is principal.
- `splitsCompletelyInSmallHilbertClassField_iff_exists_generator`: the same, as the existence of `x : Kˣ` generating the ideal of `v`.

## Caveats

`SplitsCompletelyInSmallHilbertClassField` is a reciprocity-side definition (triviality of a class in the quotient), not the decomposition behaviour of `v` in an actual field extension; the theorems are statements about ideal classes only.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/SmallHilbertSplitting.lean`: the Lean file is the source byte for byte (SHA-256 `c708a22553430fd37c38c15bad1d855565656e5ffbd6925dae78c13513840953`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
