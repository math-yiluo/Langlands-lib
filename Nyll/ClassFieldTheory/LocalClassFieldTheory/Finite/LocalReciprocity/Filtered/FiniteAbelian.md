# Filtered local reciprocity for finite abelian extensions

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian extension `L / K` of a nonarchimedean local field, this file proves filtered local reciprocity: for real `t ≥ 0`, the local Artin map sends the principal units `U_K^(⌈t⌉)` onto the upper ramification group `G^t` of `Gal(L / K)`. The proof does not depend on the characteristic. From it the file derives the tame criterion: the conductor exponent is at most `1` exactly when the residue characteristic does not divide the ramification index.

## Main results

All statements take `K, L : Type` with `K` a nonarchimedean local field and `L / K` finite abelian Galois.

- `finiteAbelian_filteredLocalReciprocity`: for `t ≥ 0`, `artinPrincipalUnitStepGroup K L t = localUpperRamificationGroup K L t`.
- `finiteAbelian_localUpperRamificationGroup_one_eq_localLowerRamificationGroup_one`: `G^1 = G_1`. The docstring notes that `φ(1)` need not be `1`; it lies in `(0, 1]`, where the upper groups are constant by filtered reciprocity, and the upper group at index `φ(1)` is `G_1`.
- `finiteAbelian_localUpperRamificationGroup_one_eq_hilbertRamificationGroup`: `G^1` is Hilbert's ramification group of the chosen valuation ring of `L` (from `chosenLocalExtensionCompleteDVF K L`), pulled back to `Gal(L / K)` along `galEquivDecompositionGroup`.
- `localConductorExponent_le_one_iff_localUpperRamificationGroup_one_eq_bot`: the conductor exponent is at most `1` exactly when `G^1` is trivial.
- `localConductorExponent_le_one_iff_hilbertRamificationGroup_eq_bot`: the same condition is triviality of Hilbert's ramification group, that is, absence of wild ramification.
- `localConductorExponent_le_one_iff_residueChar_not_dvd_ramificationIndex`: if the residue field of the chosen valuation ring of `L` has prime characteristic `p`, the conductor exponent is at most `1` exactly when `p` does not divide the ramification index of `L / K`.

## Proof of the main theorem

`L` embeds into the fixed field `F` of a standard unramified/Lubin–Tate compositum (`exists_finiteAbelianDominatingStandardLubinTateCompositum`), for which filtered reciprocity holds by `standardLubinTateFiniteAbelianCompositum_filteredLocalReciprocity`. It descends to the image `E` of `L` in `F` by `filteredLocalReciprocity_descends`, using `localUpperRamificationGroup_map_restrict`, and is transported to `L` along `L ≅ E` (`artinPrincipalUnitStepGroup_map_standardFixedFieldEquiv`, `localUpperRamificationGroup_map_autCongr`).

## Points to watch

- Only `t ≥ 0` is covered; the index `-1` is not part of the statement.
- The Artin side changes only at integers, so the main theorem implies that the upper ramification groups of `L / K` can jump only at integers; the file does not state this separately.
- The upper and lower ramification groups and Hilbert's ramification group are the library's own definitions, computed for a chosen complete discretely valued structure on `L`. The characteristic hypothesis in the tame criterion is a `CharP` instance on the residue field of that chosen valuation ring.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/FiniteAbelian.lean`: the Lean file is the source byte for byte (SHA-256 `4d2cec7c5202cc9c1365a46eb50ce368554bda4371b4ebbfd6a4742f52070559`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
