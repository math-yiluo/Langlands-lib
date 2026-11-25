# The maximal Kummer subgroup

Module `Nyll.GaloisCohomology.Kummer.Concrete.MaximalKummerSubgroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Among the subgroups of `Kˣ` containing `Kˣⁿ` (the library's `KummerSubgroup K n`), the largest is `Kˣ` itself; it corresponds to adjoining all `n`-th roots of all elements of `Kˣ`. The file defines it and identifies its radical quotient with the power-class group `Kˣ/Kˣⁿ`. `K` is any field and `n` is a positive integer (`n : ℕ+`).

- `maximalKummerSubgroup K n`: the whole unit group `⊤`, as a Kummer subgroup.
- `restrictedNthPowersSubgroup_maximal_eq`: for this subgroup, the copy of `Kˣⁿ` inside it is the image of the `n`-th power map of `⊤`.
- `maximalRestrictedRadicalQuotientEquiv`: a canonical isomorphism `Kˣ/Kˣⁿ ≃* RestrictedRadicalQuotient n (maximalKummerSubgroup K n)`.

The isomorphism is a composite of the identification of `⊤` with `Kˣ`, a quotient congruence, and the presentation of the restricted radical quotient as a quotient group. Here `Kˣ/Kˣⁿ` is written as the quotient of `Kˣ` by the range of `powMonoidHom n`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/MaximalKummerSubgroup.lean`: the Lean file is the source byte for byte (SHA-256 `368e3f9626e6d99f20e2416c9e38179464a2ccb05d4d550938eaa68bfe5d931e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
