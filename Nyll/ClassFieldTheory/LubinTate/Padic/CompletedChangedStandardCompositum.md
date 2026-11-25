# The standard–changed compositum in the completed p-adic level

Module `Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardCompositum`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Fix a prime p, a level n and a unit u of ℤ_p. Inside the completed level field `padicCompletedLevelField p n` sit two finite abelian extensions of ℚ_p: the image of the n-th standard multiplicative Lubin–Tate level, and the fixed field of the completed Frobenius lift attached to u, identified in an imported file with the changed-uniformizer level. The file forms their compositum and restricts the inverse of that Frobenius lift to it, giving the automorphism that, according to the module comment, a later norm calculation is to identify with the local Artin symbol.

## Main definitions and results

- `padicCompletedStandardLevelField p n`: the image of the standard level, with `padicStandardLevelEquivCompletedStandardLevelField` the isomorphism onto it. Instances: finite-dimensional and abelian Galois over ℚ_p; the same holds for the changed fixed field `padicCompletedChangedUniformizerFixedField p u n`.
- `padicCompletedStandardChangedCompositum p u n`: the join of the two; finite-dimensional and abelian Galois over ℚ_p, and abelian Galois over the changed fixed field.
- `padicStandardLevelToCompletedChangedCompositum`, `padicCompletedChangedFixedFieldToStandardChangedCompositum`: the inclusions of the two factors.
- `..._symm_map_standard_le`, `..._symm_map_fixedField_le`, `..._symm_map_compositum_le`: the inverse Frobenius lift maps each factor, hence the compositum, into itself; `..._symm_fixed` says it fixes the changed field pointwise.
- `padicCompletedChangedUniformizerArtinCandidate p u n`: the inverse Frobenius lift restricted to the compositum, an automorphism over ℚ_p. `..._standardLevel`: on the standard factor it acts by the unit-parameter automorphism of u. `..._fixedField`: it is the identity on the changed factor.
- `padicCompletedChangedUniformizerRelativeArtinCandidate`: the same automorphism viewed over the changed fixed field.

## Proofs

Bijectivity of the restriction follows from injectivity and finite dimension. The action on the standard factor is the imported identity relating the inverse-unit Frobenius lift to the standard level embedding.

## Watch for

- "Artin candidate" is only a name: the file does not show that this automorphism is the Artin symbol of any element.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/CompletedChangedStandardCompositum.lean`: the Lean file is the source byte for byte (SHA-256 `ad9cca8dc0a63e7ff5d205aedc6faf78a36e2e9cd3cd0f818e400750b8fe9c1a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
