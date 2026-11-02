# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk`. Statement. `AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk`: a connected,
locally noetherian scheme all of whose stalks are domains is integral.

Proof. Section `Ring`: in a noetherian ring whose localizations at primes are domains, each minimal prime has a
clopen zero locus (local `isClopen_zeroLocus_of_mem_minimalPrimes`, `compl_zeroLocus_eq_biUnion`), so every point
has an irreducible open neighbourhood (`exists_isClopen_isPreirreducible_mem_of_forall_isDomain_localizationAtPrime`).
Section `SchemeTransport` transfers this to the scheme (`exists_isOpen_mem_isPreirreducible_of_forall_isDomain_stalk`).
Section `Topology`: if every point has a preirreducible open neighbourhood, irreducible components are open and
equal to connected components (`connectedComponent_eq_irreducibleComponent_of_forall_isPreirreducible_nhd`), so a
connected such space is irreducible. An irreducible scheme with reduced (domain) stalks is integral.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.isPreirreducible_union_of_isOpen_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.isOpen_irreducibleComponent_of_forall_isPreirreducible_nhd`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.connectedComponent_eq_irreducibleComponent_of_forall_isPreirreducible_nhd`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.isPreirreducible_connectedComponent_of_forall_isPreirreducible_nhd`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.eq_of_mem_minimalPrimes_of_le_of_isDomain_localizationAtPrime`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.exists_mem_zeroLocus_minimalPrimes`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.compl_zeroLocus_eq_biUnion`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.isClopen_zeroLocus_of_mem_minimalPrimes`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.exists_isClopen_isPreirreducible_mem_of_forall_isDomain_localizationAtPrime`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.isDomain_localizationAtPrime_of_isLocalization`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.exists_primeIdealOf_eq`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.exists_isOpen_mem_isPreirreducible_of_forall_isDomain_stalk`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.N3da397ad0.isPreirreducible_connectedComponent_of_forall_isDomain_stalk`
- theorem `P2MW.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
