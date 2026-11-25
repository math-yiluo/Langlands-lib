# The ray class group at the conductor and its quotient C_K/H

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorRayClassMaximality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let H be a subgroup of the idèle class group C_K that admits a defining modulus (`ConductorialSubgroup K`), and let f be its narrow finite conductor. Then the congruence subgroup C_K^f, with positivity at every real place, lies in H. So the ray class group C_K/C_K^f maps onto C_K/H. This file studies that map. It is injective exactly when both groups have the same order. In that case H is the full congruence subgroup at its conductor, and H is determined by f.

## Main definitions and results

- `narrowFiniteConductorRayClassGroupToQuotient H`: the canonical map from the ray class group at `RayClass.Modulus.narrowOfFinite f` to C_K/H. It is surjective, its kernel is the image of H, and dividing by the kernel gives `narrowFiniteConductorRayClassSubgroupQuotientEquivIdeleClassQuotient`.
- `narrowFiniteConductorRayClassGroup_card_eq_subgroupImage_card_mul_quotient_card`: the ray class number at f equals the order of the image of H times |C_K/H|. Hence |C_K/H| divides the ray class number (`ideleClassQuotient_card_dvd_narrowFiniteConductorRayClassGroup_card`).
- `narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq`: the map is injective if and only if the two orders agree. `narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq` is the resulting isomorphism.
- `subgroup_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_quotient_card`: H equals C_K^f exactly when the two orders agree.
- `subgroups_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_quotient_cards`: two such subgroups with the same conductor, each satisfying the cardinality condition, are equal. `ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards` is the induced identification of quotients.

## Points to watch

- The uniqueness statement holds only for subgroups whose quotient has the full ray class number at their conductor, that is, for H equal to the congruence subgroup at its own narrow finite conductor, with positivity at all real places. It is not a uniqueness theorem for arbitrary subgroups with a given conductor.
- The ray class group is taken at the narrow modulus, with positivity at all real places, whatever the archimedean part of the conductor of H is.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ConductorRayClassMaximality.lean`: the Lean file is the source byte for byte (SHA-256 `af4e88837e77bab051e29998104e36937927e4f334fd56ff20730d69f49888e3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
