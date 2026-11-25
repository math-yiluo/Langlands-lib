# When the norm group is the full ray congruence subgroup of its conductor

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormRayClassMaximality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields, `N(C_L)` the image of the idèle-class norm, and `f` its narrow finite conductor `ideleClassNormNarrowFiniteConductor`. The ray congruence subgroup of the narrow modulus built from `f` lies in `N(C_L)`, so the ray class group of that modulus surjects onto `C_K ⧸ N(C_L)`. The file characterizes when this surjection is an isomorphism, that is, when `N(C_L)` is the whole congruence subgroup.

## Main results

- `ideleClassNorm_range_eq_narrowConductorSubgroup_iff_rayClass_card_eq_normQuotient_card`: `N(C_L)` equals the congruence subgroup of the narrow modulus of `f` if and only if the ray class group of that modulus and `C_K ⧸ N(C_L)` have the same order. One subgroup contains the other, and a strict inclusion would strictly drop the index.
- `narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_injective_iff_card_eq_normQuotient_card`: the canonical surjection is injective if and only if the two orders agree.
- `normQuotientEquivNarrowFiniteConductorRayClassGroup`: under that equality of orders, the isomorphism `C_K ⧸ N(C_L) ≃* RayClassGroup` given by equality of subgroups.
- `ideleClassNorm_ranges_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_normQuotient_cards`: two finite Galois extensions `L` and `M` of `K` with the same narrow finite conductor, each satisfying this equality of orders, have the same norm group.
- `normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards`: in that situation, the isomorphism of their norm quotients that fixes idèle-class representatives (`_mk`).
- `normRayClassMaximalityClassGroupIsMulCommutative`: commutativity of the idèle class group, used as a local instance.

## Points to watch

- The equality of orders is one side of the first two equivalences and a hypothesis of the remaining results; the file does not say when it holds. These are criteria, not a theorem that every norm group is a full ray congruence subgroup.
- The modulus is narrow: its infinite part contains every real place, whatever the ramification at infinity.
- Orders are `Nat.card`; finiteness of the groups comes from the imported results.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/NormRayClassMaximality.lean`: the Lean file is the source byte for byte (SHA-256 `82af9ad80d78b093f5f66838768ce6aaadc9b46d5ff1486acafd7508498590f4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
