# The maximal exponent-n Kummer extension of a local field is finite

Module `Nyll.GaloisCohomology.Kummer.Concrete.LocalMaximalKummerExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K` containing a primitive `n`-th root of unity, with `n` a positive integer that is nonzero in `K`, adjoining to `K` all `n`-th roots of all elements of `Kˣ` gives a finite extension.

- `finite_maximalRestrictedRadicalQuotient`: if `(n : K) ≠ 0`, the radical quotient of the maximal Kummer subgroup, that is `Kˣ/Kˣⁿ`, is finite.
- `maximalKummerRadicalExtension_finiteDimensional`: if moreover `K` contains a primitive `n`-th root of unity, the radical extension `kummerRadicalExtension n (maximalKummerSubgroup K n)` inside a separable closure `Ω` of `K` is finite-dimensional over `K`.

The first result transports the finiteness of `Kˣ/Kˣⁿ` (proved elsewhere in the library for local fields with `n` nonzero in `K`) along the isomorphism with the maximal radical quotient; the second applies the criterion that a finite radical quotient gives a finite radical extension, which rests on the Kummer pairing.

The finiteness of the extension uses the primitive-root hypothesis; the finiteness of `Kˣ/Kˣⁿ` does not. Local fields are in the sense of the library's `IsNonarchimedeanLocalField`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/LocalMaximalKummerExtension.lean`: the Lean file is the source byte for byte (SHA-256 `dd2880aeedf0babb4e15017e9d89178fb3a31690f48b8f814cd3f392d151a0d9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
