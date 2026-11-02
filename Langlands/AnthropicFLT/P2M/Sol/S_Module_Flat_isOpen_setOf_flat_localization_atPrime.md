# `Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_isOpen_setOf_flat_localization_atPrime`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_Flat_isOpen_setOf_flat_localization_atPrime.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_isOpen_setOf_flat_localization_atPrime`. Statement. `Module.Flat.isOpen_setOf_flat_localization_atPrime` (openness of the flat locus): for a finite type algebra `B` over
a noetherian ring `A`, the set of primes `Q` of `B` with `B_Q` flat over `A` is open.

Proof. Sections `Tors`, `FlatIff`: by the ported local criterion `Module.flat_of_comap_maximalIdeal_rTensor_injective`,
`B_Q` is flat iff a certain torsion module vanishes at `Q` (`tors_of_flat`, `flat_of_tors`). Section `Nagata`: it is
enough to show that the locus contains a nonempty open subset of every irreducible closed set it meets
(`isOpen_of_nagata`). Sections `Fibre`, `FibreAway`, `Step`: on `V(𝔮)` this follows from generic flatness over `A/𝔮` (ported
`Module.Flat.exists_ne_zero_flat_localization_tensorProduct`) together with a uniform killer of the relevant torsion
(`exists_uniform_killer`, `flat_fibre_away`, `fibre_step`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.K`
- lemma `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.mem_K`
- theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.injective_lTensor_iff`
- lemma `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.injective_rTensor_iff`
- def `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.Tors`
- lemma `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.Tors.mono`
- theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.tors_of_flat`
- theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.flat_of_tors`
- theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.flat_of_le`
- theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.isOpen_of_nagata`
- theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.exists_uniform_killer`
- theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.flat_fibre_away`
- theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.injective_lTensor_away`
- theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.fibre_step`
- theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.OpenFlatLocus.isOpen_flatLocus`
- theorem `P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_exists_ne_zero_flat_localization_tensorProduct` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective` (same contribution).
Other imports: `Mathlib`.
