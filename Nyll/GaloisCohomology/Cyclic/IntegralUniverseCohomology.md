# Integral group cohomology for independent group and carrier universes

Module `Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a group G in `Type u` and an integral representation `A : Rep.{v} ℤ G` whose carrier lies in another universe v, the file defines integral group cohomology, homology and (for finite G) Tate cohomology by lifting G and A to the universe `max u v` and applying the same-universe construction of `IntegralGroupCohomology`. It records the connecting maps and identifies the result with the same-universe objects, and in universe 0 with Mathlib's.

## Main definitions and results

All are in the namespace `IntegralGroupCohomology.Universe`.

- `nativeFunctor G : Rep.{v} ℤ G ⥤ Rep.{max u v} (ULift ℤ) (ULift G)` composes the library's `Rep.universeLiftFunctor` with the coefficient transport `IntegralGroupCohomology.coefficientFunctor`; it is additive. Lemmas say that after removing the lifts the action, the maps, the degree-one coboundary and the norm are the original ones.
- `cohomologyFunctor G n`, `homologyFunctor G n`, `tateFunctor G n` (finite G, n ∈ ℤ), and the objects `cohomology A n`, `homology A n`, `tate A n`, all ℤ-modules in `ModuleCat.{max u v} ℤ`.
- `δ` and `tateδ`, the connecting maps of a short exact sequence of representations, and their naturality `δ_naturality`, `tateδ_naturality`.
- When the carrier is in the universe of G: `cohomologyIsoCommon`, `homologyIsoCommon` and `tateIsoCommon` identify these objects with `IntegralGroupCohomology.cohomology`, `.homology` and `.tate`, through the group isomorphism `ULift G ≃* G` and the carrier isomorphism `nativeCarrierEquiv`.
- In universe 0: `cohomologyIsoOriginal`, `homologyIsoOriginal` and `tateIsoOriginal` identify them with Mathlib's `groupCohomology A n`, `groupHomology A n` and `tateCohomology A n`; `finite_tate_iff_original`, `card_tate_eq_original` and `isZero_tate_iff_original` transfer finiteness, cardinality and vanishing.

## Proof

The connecting maps and naturality are those of the same-universe construction applied to the lifted short exact sequence (`Rep.universeLiftFunctor_shortExact`). The common-universe comparisons apply the functoriality of group (co)homology and Tate cohomology along a group isomorphism and an intertwining carrier isomorphism (`groupCohomology.mapIso`, `groupHomology.mapIso`, `TateCohomology.groupEquivIso`); the universe-0 comparisons compose these with those of the same-universe file.

## Watch for

- These objects are the library's own. They agree with Mathlib's group cohomology only through the explicit isomorphisms, which exist only in universe 0; in general they are defined via lifts to `max u v`.
- The comparisons with Mathlib cover cohomology, homology and Tate groups as modules; for the connecting maps, the compatibility with Mathlib's is proved only in the same-universe file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/IntegralUniverseCohomology.lean`: the Lean file is the source byte for byte (SHA-256 `74fe45ec41bc8b021d5840ec100e527a10cde0e433dce00ce9084503cf7bbe79`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
