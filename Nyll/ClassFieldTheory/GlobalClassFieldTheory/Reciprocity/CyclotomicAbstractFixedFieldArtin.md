# The cyclotomic unramified Artin map over abstract fixed fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicAbstractFixedFieldArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file works in abstract class field theory over ℚ, with the absolute Galois group `Gal(ℚ^sep/ℚ)` and the cyclotomic degree datum `rationalCyclotomicDegreeData`. For a finite abstract field `H` (a closed subgroup of finite index), let F be its fixed field and U the fixed field of the "field inertia" of `H`, the kernel of the normalized degree on `H`. Then U is F composed with the cyclotomic ℤ̂-extension `rationalCyclotomicZHatField` of ℚ. The file identifies Gal(U/F) with ℤ̂, computes the library's infinite global Artin map of U/F in that coordinate, and matches it with the abstract norm residue symbol.

## Main definitions and results

- `abstractFixedFieldCyclotomicGalEquivZHat H`: Gal(U/F) ≃* `Multiplicative ZHat`, through the normalized degree; simp lemmas evaluate it on representatives. `abstractFixedFieldCyclotomic_isAbelianGalois`: U/F is abelian Galois.
- `abstractFixedFieldCyclotomicRestriction`: restriction Gal(U/F) → Gal(T/ℚ), T the cyclotomic ℤ̂-field. `..._coordinate`: in ℤ̂ coordinates it is multiplication by the residue degree of `H`.
- For each finite Galois layer E of T/ℚ, the compositum F·E as a finite abelian layer of U/F (`abstractFixedFieldCyclotomicFiniteGaloisLayer`), with restriction compatible with restriction to E.
- `abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom` (simp): restricting `infiniteGlobalArtinMonoidHom F U a` to T gives `rationalCyclotomicZHatGlobalArtin` of the idele norm of a from F to ℚ.
- `abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom`: the ℤ̂ coordinate of the Artin symbol of a is `normalizedCyclotomicZHatIdeleValue F a`; a `_mk` version uses the value on idele classes.
- `infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele` (simp): principal ideles map to 1. Hence `abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom`, the map C_F → Gal(U/F), whose ℤ̂ coordinate is the normalized idele-class value.
- `abstractFixedFieldCyclotomicIdeleClassArtin_eq_maximalUnramifiedNormResidue`: transported by `rationalAbstractFixedFieldIdeleClassEquivFixed`, this map equals the abstract maximal-unramified norm residue symbol of `rationalCyclotomicIdeleClassValuationData`.
- `abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_prime`: a prime element (valuation 1) maps to the Frobenius of `H`.

## Proofs

The restriction theorem is checked on every finite layer E, using norm functoriality of the global Artin maps (`globalArtinMonoidHomOfNumberField_norm_restriction`), and assembled by injectivity of the map from Gal(T/ℚ) to the inverse limit of its finite quotients. The coordinate formula follows after multiplying by the residue degree, which is positive and injective on ℤ̂, and using that the intersection degree of F with T is that residue degree. The comparison with the norm residue symbol and the Frobenius statement only compare valuation coordinates; no finite reciprocity comparison is assumed.

## Watch for

- "Maximal unramified" is meant in the abstract sense: U is the fixed field of the kernel of the cyclotomic degree on `H`, not the arithmetic maximal unramified extension of F.
- `infiniteGlobalArtinMonoidHom` is the library's own Artin map, built from chosen local factors.
- The ℚ-algebra structure on `SeparableClosure ℚ` is fixed locally as `DivisionRing.toRatAlgebra`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/CyclotomicAbstractFixedFieldArtin.lean`: the Lean file is the source byte for byte (SHA-256 `29ac532c8fc7beaf2638fbe03a4734e16d82bea95bb144cb064018e67f2baf10`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
