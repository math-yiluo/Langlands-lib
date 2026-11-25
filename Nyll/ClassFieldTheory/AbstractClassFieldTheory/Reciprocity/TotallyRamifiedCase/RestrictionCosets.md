# Restriction from an auxiliary unramified tower to a totally ramified extension

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory over a topological group `G` with degree map `D`, let E/K be an extension of abstract fields and M ⊇ E a finite Galois extension of K, with M₀ the maximal unramified subextension of M/K. This file compares G(M/M₀) with the coset space of E in K (the group G(E/K) when E/K is normal) and deduces how actions and norms from M to M₀ restrict to E.

## Definitions and results

- `bundledRestrictionHom`: restriction G(M/K) → G(L/K) between finite Galois subextensions with M ⊇ L.
- `abstractReciprocityRestrictionCosetMap`: the map from G(M/M₀) to the coset space of E in K, induced by the inclusion of the subgroup of M₀ into that of K. `abstractReciprocityRestrictionCosetMap_bijective`: it is bijective when E/K is totally ramified (`hTot`) and every inertia element of K that fixes E also fixes M (`hInertia`). The bijection is packaged as `abstractReciprocityRestrictionCosetEquiv`, and as a group isomorphism `abstractReciprocityRestrictionMulEquiv` when E/K is normal.
- `relativeCosetAction_abstractReciprocityRestrictionCosetEquiv`: on A_E viewed in A_M, the action of an element of G(M/M₀) equals the action of its image.
- `abstractReciprocity_relativeNorm_fixedFieldInclusion`: for E/K finite, under the same hypotheses, the norm of a from M to M₀ equals its norm from E to K for a ∈ A_E, both read among the M₀-fixed elements. The proof reindexes the sum over cosets by the bijection.
- `commute_of_same_restriction_of_inertia_le`: if the inertia subgroup of E lies in the subgroup of M (`hIE`) and E/K is normal, two elements of G(M/K) with the same restriction to E commute: their commutator has trivial degree and fixes E, so it fixes M.
- `relativeCosetAction_eq_of_restriction_eq`: for E/K normal, two elements of G(M/K) with the same restriction to E act equally on A_E.

## Points to watch

- The inclusion conditions are in subgroup order: `M.field.toSubgroup ≤ E.field.toSubgroup` means M ⊇ E as fields.
- The coset map is a bijection of sets in general; the group isomorphism needs E/K normal.
- `hInertia` and `hIE` are hypotheses on M that the caller must supply.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean`: the Lean file is the source byte for byte (SHA-256 `f3693068a820c3d7623c842af51835cea02fa3edf7078821c4f6f4465940f446`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
