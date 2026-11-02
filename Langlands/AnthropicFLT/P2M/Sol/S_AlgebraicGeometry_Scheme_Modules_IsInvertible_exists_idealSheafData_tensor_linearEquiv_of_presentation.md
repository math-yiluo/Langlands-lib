# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation`. Statement. `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_idealSheafData_tensor_linearEquiv_of_presentation`: given
an invertible module `M` on an integral scheme with an embedding `φ` into the function field (as in
`exists_functionField_presentation`), there are nonzero ideal sheaves `I` ("denominators") and `J`
("numerators") and, on every affine open `U`, isomorphisms `e U : I(U) ⊗ M(U) ≅ J(U)` compatible with
restriction, such that `a ∈ I(U)` iff `a · φ(m)` is integral for all `m`, and `e U (a ⊗ m) = a · φ(m)` in the
function field (writing `M ≅ J ⊗ I⁻¹`).

Proof (namespace `P2mDenomAlg`). Section `Denom` (commutative algebra over a domain `R` with fraction field
`K` and an injective `R`-linear `φ : M → K`, `M` finite projective of rank one): the denominator ideal
`denom` (elements `a` with `a φ(M) ⊆ R`), nonzero (`exists_mem_denom`); the multiplication map
`mulMap : denom ⊗ M → R`, injective (flatness), with image the numerator ideal `numer` (`range_mulMap_eq_span`,
`numerMap_injective`), giving `equiv`. Section `Loc`: these constructions commute with localization at
basic opens (`map_denom_eq`, `range_mulMap_loc`, `map_numer_eq_loc`). Section `Geom`: sections of `M` over
affine opens are finite projective (ported `Scheme.Modules.projective_sections_of_locallyTrivial`,
`OModulePresheaf.isCoherent_ofModules_of_locallyTrivial`, `…isQuasicoherent…`), so the affine-local ideals
form ideal sheaves `I` and `J` with the stated properties.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.intLocus`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.denom`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.mem_denom`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.mem_denom_of_span`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.exists_mem_denom`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.mulMap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.mulMap_tmul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.mulMap_injective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.isInteger_mulMap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.range_mulMap_le`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.gens`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.range_mulMap_eq_span`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.numer`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.mem_numer`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.map_numer_eq`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.numerMap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.numerMap_injective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.range_mulMap_eq_range_numerMap`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.equiv`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.algebraMap_equiv`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.numer_ne_bot`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.map_denom_le`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.denom_le_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.map_denom_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.map_linearMap_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.range_mulMap_loc`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.map_numer_eq_loc`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.toSpecTop`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.finite_sections`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.flat_sections`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.res_surj`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.nonempty_of_le`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.eq_bot_of_not_nonempty`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.subsingleton_of_not_nonempty`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.genericPoint_mem`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.algebraMap_res`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.isScalarTower_basicOpen`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.φlin`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.φlin_apply`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.idealI`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.idealJ`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.idealI_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.idealJ_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.idealI_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.idealJ_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.map_ideal_basicOpen`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.sheafI`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.sheafJ`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.sheafI_ideal`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.sheafJ_ideal`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.exists_apply_ne_zero`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.ePos`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.algebraMap_ePos_tmul`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.eEmpty`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.eAll`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.eAll_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.P2mDenomAlg.main`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial` (Library).
Other imports: `Mathlib`.
