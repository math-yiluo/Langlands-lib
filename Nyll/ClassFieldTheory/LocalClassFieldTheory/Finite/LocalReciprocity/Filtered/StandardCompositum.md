# Filtered reciprocity for the standard unramified–Lubin–Tate compositum

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.StandardCompositum`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

`standardLubinTateFiniteAbelianCompositum_filteredLocalReciprocity`: let `K` be a nonarchimedean local field (`K : Type`), `d > 0`, `n` a natural number and `t ≥ 0` real. For the fixed field `F` of `standardLubinTateFiniteAbelianCompositum K d n hd`, the Artin principal-unit step group at `t` equals the upper ramification group at `t`.

Proof: `F` is the compositum of `E₁`, the canonical unramified factor of degree `d`, and `E₂`, the standard Lubin–Tate level `n - 1` factor (`standardLubinTateFiniteAbelianCompositum_fixedField_eq_sup`). On `E₁` both filtrations vanish (`artinPrincipalUnitStepGroup_finiteUnramifiedAbelianExtension_eq_bot`, `localUpperRamificationGroup_finiteUnramifiedAbelianExtension_eq_bot`). On `E₂` filtered reciprocity is the imported `standardLubinTateFiniteAbelianSubextension_filteredLocalReciprocity`, and `filteredLocalReciprocity_of_compositum` combines the two.

The Lubin–Tate case is used here, not proved. Only indices `t ≥ 0` are covered. The header stresses that the compositum is built the same way in every characteristic.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/StandardCompositum.lean`: the Lean file is the source byte for byte (SHA-256 `3eb91c97594cd489d10c7e9b1eaedbe1d1974af0a4ecac70d2e4fdd3cfcff5eb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
