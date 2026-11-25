# Filtered local reciprocity for standard Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardFilteredArtinComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a nonarchimedean local field and L_n the n-th level of the standard Lubin–Tate tower over K (`standardLubinTateLevelField hπ n`), built on the canonical uniformizer of `standardLocalField K`. The file proves filtered local reciprocity for these abelian extensions: for every real t ≥ 0, the Artin image of the unit group U_K^(⌈t⌉) is the upper ramification group G^t of Gal(L_n/K). The Artin map is the universe-polymorphic `Universe.abelianLocalArtinMonoidHom`.

## Main results

- `standardLubinTateNormSubgroup_map_artin_eq_restrictKer`: for any uniformizer π and m ≤ n, the Artin image in Gal(L_n/K) of the norm group of L_m is the kernel of restriction to L_m. `standardLubinTateBaseUniformizerUnit_zpowers_le_artinKer`: the powers of π lie in the Artin kernel.
- `standardLubinTateCanonicalArtinPrincipalUnitsImage_eq_restrictKer`: for the canonical uniformizer, the Artin image of U_K^(m+1) is that restriction kernel.
- `standardLubinTateCanonicalArtinPrincipalUnitsImage_eq_localUpperRamificationGroup`: for 1 ≤ k ≤ n + 1, `artinPrincipalUnitGroup K L k` (the image of U_K^(k)) equals `localUpperRamificationGroup K L k`.
- `standardLubinTateCanonicalLocalUpperRamificationGroup_succ_eq_bot` and `standardLubinTateCanonicalArtinPrincipalUnitGroup_succ_eq_bot`: both are trivial at index n + 1.
- Index zero: `standardLubinTateRealLowerRamificationGroup_zero_eq_top` and `standardLubinTateRealUpperRamificationGroup_zero_eq_top` (the explicit ramification groups are everything at 0, for any `LocalField` structure on K and any uniformizer), `standardLubinTateLocalUpperRamificationGroup_zero_eq_top`, `standardLubinTateCanonicalArtinPrincipalUnitGroup_zero_eq_top` (the units of 𝒪_K map onto the Galois group) and `..._ArtinPrincipalUnitStepGroup_zero_eq_localUpper`.
- Beyond the last jump: `..._ArtinPrincipalUnitStepGroup_eq_bot_of_level_lt_ceil` and `..._LocalUpperRamificationGroup_eq_bot_of_level_lt_ceil`, for n + 1 < ⌈t⌉.
- `standardLubinTateCanonicalArtinPrincipalUnitStepGroup_eq_localUpperRamificationGroup`: for every real t ≥ 0, `artinPrincipalUnitStepGroup K L t = localUpperRamificationGroup K L t`.
- Helpers: `map_composite_ker_eq_ker_of_surjective` (group theory) and two index lemmas comparing ⟨π⟩ · U^(n+1) with the norm subgroup.

## Proof

The Artin image of the norm group of L_m is the restriction kernel, by compatibility of the Artin map with restriction and surjectivity. The imported equality of the norm group of L_m with ⟨π⟩ · U_K^(m+1) (`standardLubinTateCanonicalUniformizerPrincipalSubgroup_eq_normSubgroup`), together with π lying in the kernel, leaves the image of U_K^(m+1). The explicit computation `standardLubinTateRealUpperRamificationGroup_eq_restrictKer` identifies the restriction kernel with the upper ramification group; the real index is reduced to ⌈t⌉ by `standardLubinTateRealUpperRamificationGroup_eq_natCeil`.

## Caveats

- The main results concern the canonical uniformizer of `standardLocalField K`; only the first two statements and the three `..._zero_eq_top` statements on ramification groups are for an arbitrary uniformizer.
- `artinPrincipalUnitStepGroup` uses the step filtration t ↦ U^(⌈t⌉), and `localUpperRamificationGroup` is the library's upper numbering; both are library notions.
- The module docstring stresses that no norm-subgroup equality or containment is a hypothesis; the norm-group equality is imported as a proved theorem.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/LubinTateApplication/StandardFilteredArtinComparison.lean`: the Lean file is the source byte for byte (SHA-256 `6291f76ec9e1b65da5f13a511b05e3e831fede48bc245f72c46e1878a2dd5322`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
