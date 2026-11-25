# Kummer theory: recovering an extension from its radical group

Module `Nyll.GaloisCohomology.Kummer.Concrete.ExtensionRoundTrip`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `Ω` be a field over `K` and `E` an intermediate field, with `E/K` Galois, `Gal(E/K)` commutative and killed by `n`, and `K` containing a primitive `n`-th root of unity. Let `Δ_E` (`finiteKummerRadicalSubgroup`) be the group of `a ∈ Kˣ` having an `n`-th root in `E`.

- `kummerRadicalExtension_finiteKummerRadicalSubgroup_eq`: adjoining to `K` all `β ∈ Ω` with `βⁿ ∈ Δ_E` gives back `E`.
- `kummerRadicalExtension_finiteKummerRadicalSubgroup_le` (and `kummerRootSet_finiteKummerRadicalSubgroup_le`): the inclusion into `E`, which needs only the root of unity. An `n`-th root in `Ω` of `a ∈ Δ_E` differs from one in `E` by an `n`-th root of unity, which lies in `K`.
- `le_kummerRadicalExtension_finiteKummerRadicalSubgroup`: the reverse inclusion, from the library's generation theorem `kummerRootSet_adjoin_eq_top` applied to `E/K`.

`E/K` need not be finite, and `Ω` is not assumed algebraically closed. The radical extension `kummerRadicalExtension` and root set `kummerRootSet` are the library's own constructions from another file. This is one round trip of the Kummer correspondence: extension to radical group and back.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/ExtensionRoundTrip.lean`: the Lean file is the source byte for byte (SHA-256 `89971baeddeeb8246aa8f5e43c0f25309baaaca0922e33ae15a044c8278cf61b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
