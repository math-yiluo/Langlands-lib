# The standard local-field package of a nonarchimedean local field

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field K given through Mathlib's topology-first interface (`ValuativeRel K`, a topology, `IsNonarchimedeanLocalField K`), the Lubin–Tate files work with the library's own `LocalField` structure, a complete discrete valuation with finite residue field. This file packages the canonical valuation of K as such a structure and identifies its valuation ring, maximal ideal, units and principal-unit filtration with the topology-first objects 𝒪[K], 𝓂[K], `principalUnits` and `LocalFieldTheory.fieldPrincipalUnits`.

## Main definitions

- `standardLocalField K`: the `LocalField K` built from `LocalFieldTheory.localCompleteDVF K`.
- `standardLocalFieldIntegerEquiv K`: the ring isomorphism 𝒪[K] ≃ valuation ring of the package, the identity on elements; `standardLocalFieldIntegerUnitsEquiv K` is the induced isomorphism of unit groups.
- `standardLocalFieldValuationUnitsToFieldUnits K`: the inclusion of the package's valuation-ring units into Kˣ.
- `standardLocalFieldUniformizer K`: the library's chosen uniformizer of 𝒪[K], transported to the package.

## Main results

- `standardLocalField_valuation_eq`: the package's valuation is `ValuativeRel.valuation K`; `standardLocalField_residueField_natCard`: its residue field has the cardinality of 𝓀[K].
- `standardLocalFieldIntegerEquiv_map_maximalIdeal`, `_map_maximalIdeal_pow`, `_mem_maximalIdeal_pow_iff`: the isomorphism carries 𝓂[K]^n onto the n-th power of the package's maximal ideal.
- `standardLocalFieldIntegerUnitsEquiv_mem_higherPrincipalUnitGroup_iff`, `standardLocalFieldHigherPrincipalUnitGroup_map_eq_principalUnits`: the library's higher principal units U^n of the package correspond exactly to `principalUnits K n`.
- `standardLocalFieldHigherPrincipalUnitGroup_map_eq_fieldPrincipalUnits`, `standardLocalFieldValuationUnit_mem_fieldPrincipalUnits_iff_mem_higher`: the same inside Kˣ, with `LocalFieldTheory.fieldPrincipalUnits K n`.
- `standardLocalFieldUniformizer_isUniformizer`: the transported element is a uniformizer for the package's valuation.

## Watch for

- Two parallel interfaces coexist: the library's `LocalField` / `CompleteDVF` structures and Mathlib's `IsNonarchimedeanLocalField`. This file is the bridge between them; the identifications are proved, mostly by the identity on underlying elements.
- `standardLocalFieldUniformizer` is a fixed choice inherited from `chosenIntegerRingUniformizer`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`: the Lean file is the source byte for byte (SHA-256 `a38f03518ee7fb3b57b10d7a5760c8e1f2713eb8f08b1ad1aff35b0554545858`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
