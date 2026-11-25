# Standard Lubin–Tate factors for finite local existence

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardLubinTate`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K`, the standard Lubin–Tate level fields are already intermediate fields of `SeparableClosure K`. This file packages them as abstract finite abelian subextensions, computes their norm subgroups, and combines them with the canonical unramified factors into the standard composita used in the local existence theorem. The header notes that this construction works in every characteristic.

## Main definitions and results

Throughout, `ϖ` is the fixed unit `inverseIntegerRingUniformizerFieldUnit K`, and `uniformizerPrincipalSubgroup K ϖ d n` is the standard subgroup written `⟨ϖ^d⟩ U_K^n` in the docstrings.

- `standardLubinTateFiniteAbelianSubextension K m`: the standard Lubin–Tate level-`m` field `standardLubinTateLevelField hπ m`, where `hπ` is the proof `standardLocalFieldUniformizer_isUniformizer K` of the uniformizer property, as an abstract finite abelian subextension through its inclusion into `SeparableClosure K`.
- `standardLubinTateFiniteAbelianSubextensionFixedFieldEquiv K m`: a `K`-algebra isomorphism between the level field and the fixed field this subextension represents.
- `standardLubinTateFiniteAbelianSubextension_normSubgroup_map_eq`: its norm subgroup, transported to `Kˣ`, is exactly `⟨ϖ⟩ U_K^(m+1)`. This rests on the imported `standardLubinTateCanonicalNormSubgroup_eq_normalizedUniformizerPrincipalSubgroup`.
- `standardLubinTateFiniteAbelianCompositum K d n hd`: the compositum of the canonical unramified degree-`d` factor `localFiniteUnramifiedAbelianSubextension K d hd` with the Lubin–Tate level `n - 1`.
- `standardLubinTateFiniteAbelianCompositum_fixedField_eq_sup`: its fixed field is the compositum of the two fixed fields.
- `standardLubinTateFiniteAbelianCompositum_nativeNormSubgroup_le`: for `d, n > 0` and a subgroup `H ≤ Kˣ` containing `⟨ϖ^d⟩ U_K^n`, the ordinary norm subgroup of the standard compositum lies in `H`.

## Proof of the last result

The unramified factor has norms in `unramifiedNormSubgroup K d` (`localFiniteUnramifiedAbelianSubextension_normSubgroup_map_le`), the Lubin–Tate factor has norms in `⟨ϖ⟩ U_K^n` by the equality above, and `ϖ` has normalized valuation `1`. The subgroup calculation `finiteAbelianCompositum_normSubgroup_le_of_standard` then bounds the norms of the compositum, and the bound is transported to `Kˣ`.

## Points to watch

- Index shift: the compositum uses level `n - 1`, matching principal units `U_K^n`. With natural subtraction, `n = 0` also gives level `0`; the containment result therefore requires `0 < n`.
- `ϖ` is one specific unit of normalized valuation `1`, not an arbitrary uniformizer.
- The first two definitions allow `K` in any universe; the norm comparisons, the compositum and its fixed-field theorem take `K : Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardLubinTate.lean`: the Lean file is the source byte for byte (SHA-256 `ad09c692efcf5e356c31118c25cd3300fe1cf6f2e3e84106c9bc2357670ea8f2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
