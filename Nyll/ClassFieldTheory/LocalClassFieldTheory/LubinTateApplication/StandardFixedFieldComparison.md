# Filtered reciprocity for the Lubin–Tate level inside the separable closure

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardFixedFieldComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The canonical standard Lubin–Tate level of a nonarchimedean local field K appears in local existence theory as a finite abelian subextension `standardLubinTateFiniteAbelianSubextension K m` of `SeparableClosure K`, with fixed field M. The file transfers filtered local reciprocity from the level field to M along their K-algebra isomorphism.

## Main results

- `artinPrincipalUnitStepGroup_map_standardFixedFieldEquiv`: for finite abelian extensions L and M of K and e : L ≃ₐ[K] M, conjugation by e carries the Artin step group `artinPrincipalUnitStepGroup K L t` onto that of M; this rests on `Universe.abelianLocalArtinMonoidHom_autCongr`.
- `standardLubinTateFiniteAbelianSubextension_filteredLocalReciprocity`: for every real t ≥ 0, `artinPrincipalUnitStepGroup K M t = localUpperRamificationGroup K M t`, i.e. the Artin image of U_K^(⌈t⌉) is the upper ramification group G^t of Gal(M/K).

## Proof

The equality holds for the standard level field E by the filtered comparison for standard levels; both filtrations are transported along `standardLubinTateFiniteAbelianSubextensionFixedFieldEquiv K m : E ≃ₐ[K] M`, using `localUpperRamificationGroup_map_autCongr` for the upper numbering.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/LubinTateApplication/StandardFixedFieldComparison.lean`: the Lean file is the source byte for byte (SHA-256 `3acd74dfd9c6265dc30a84c6b2818ddfa196161d48f3acaaabfe2114813fde86`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
