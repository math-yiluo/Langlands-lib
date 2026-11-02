# `Langlands.AnthropicFLT.P2M.Sol.S_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof. `Spec K ⟶ Spec R` is an open immersion (`K = R[1/ϖ]`, `codim1Local_isLocalizationAway`).
The stalk of `T` at `η` is a discrete valuation ring
(`AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes`), whose generic
point `ξ` lies in the generic fibre. On the open irreducible component `U₀` of `η`
(`AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk`), an integral scheme, `uK`
defines a partial map to `X` over `Spec R`; since `f` is proper it satisfies the existence part of
the valuative criterion, so the partial map is defined at `η`
(`AlgebraicGeometry.Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk`). Its domain
is the required neighbourhood, and separatedness gives agreement with `uK` on the generic fibre.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private theorem `P2MW.S_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth.codim1Local_isLocalizationAway`
- theorem `P2MW.S_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk` (same contribution).
Other imports: `Mathlib`.
