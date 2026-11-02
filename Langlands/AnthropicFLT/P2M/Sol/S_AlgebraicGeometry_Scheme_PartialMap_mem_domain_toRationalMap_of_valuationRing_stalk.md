# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `ValuativePartialMap`). The stalk `O_{X,x}` is a valuation ring with fraction
field the function field of `X`. The partial map gives `Spec (function field) ⟶ Y`, and
`Spec O_{X,x} ⟶ X ⟶ S` completes a valuative square for `sY`; the existence part of the valuative
criterion gives a lift `Spec O_{X,x} ⟶ Y`. The lift defines a partial map on a neighbourhood of `x`
(`Scheme.PartialMap.ofFromSpecStalk`) with the same restriction to the generic point, hence the
same rational map (`Scheme.RationalMap.eq_of_fromFunctionField_eq`), so `x` is in the domain. The
auxiliary lemmas compare morphisms from spectra of stalks along specializations.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.ValuativePartialMap.fromSpecStalkOfMem_eq_of_specializes`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.ValuativePartialMap.partialMap_fromSpecStalkOfMem_eq_of_specializes`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.ValuativePartialMap.partialMap_fromFunctionField_eq_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.ValuativePartialMap.ofHom_algebraMap_stalk_functionField`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.ValuativePartialMap.existence_of_universallyClosed`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
