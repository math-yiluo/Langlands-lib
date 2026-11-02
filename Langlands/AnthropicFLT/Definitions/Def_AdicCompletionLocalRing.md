# `Langlands.AnthropicFLT.Definitions.Def_AdicCompletionLocalRing`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AdicCompletionLocalRing.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The `𝔪`-adic completion of a noetherian local ring (namespace `AdicCompletion`).

- Section `Kernel` (for an ideal `I` of `A`): `evalₐ_algebraMap` (the projection
  `evalₐ I n : Â → A ⧸ Iⁿ` sends the image of `a` to its class), `mem_ker_evalₐ_iff`, and for
  finitely generated `I`: `ker_evalₐ_eq_map_pow` (the kernel of `evalₐ I n` is `Iⁿ Â`),
  `exists_eq_algebraMap_add` (every element of `Â` is the image of some `a ∈ A` plus an element of
  `Iⁿ Â`), `isUnit_one_add_of_mem_map` and `isUnit_add_of_mem_map` (`1 + x` and `u + x` are units for
  `x ∈ I Â` and a unit `u`).
- Section `Local` (for a local ring `A`): `isUnit_of_isUnit_algebraMap`; for noetherian `A`:
  `maximalIdeal_fg`, the instance `instIsLocalRingMaximalIdeal` (the completion is local),
  `maximalIdeal_pow_eq_ker_evalₐ` (`𝔪̂ⁿ = ker evalₐ n`), `maximalIdeal_eq_ker_evalₐ_one`,
  `mem_maximalIdeal_iff`, and, for a ring `k` with `Algebra k A`, the `k`-algebra isomorphism
  `quotientMaximalIdealPowAlgEquiv k n : Â ⧸ 𝔪̂ⁿ ≃ₐ[k] A ⧸ 𝔪ⁿ` (`quotientMaximalIdealPowAlgHom` and
  its bijectivity, with `_mk` lemmas).
- Section `Transport`: for a `k`-algebra isomorphism `Φ : Â ≃ₐ[k] B` to a local ring `B`, the
  maximal ideal of `B` is the image of `𝔪` (`comap_maximalIdeal_algEquiv`,
  `map_maximalIdeal_algEquiv`, `maximalIdeal_eq_map_algEquiv`, `maximalIdeal_pow_eq_map_algEquiv`,
  `algEquiv_algebraMap_mem_maximalIdeal`, `isUnit_algEquiv_iff`), and
  `quotientMaximalIdealPowAlgEquivOfAlgEquiv Φ n : B ⧸ 𝔪_Bⁿ ≃ₐ[k] A ⧸ 𝔪ⁿ` with its value on images
  of `A`.
- The file ends with `#print axioms` commands for seven of these declarations.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AdicCompletion.evalₐ_algebraMap`
- theorem `AdicCompletion.mem_ker_evalₐ_iff`
- theorem `AdicCompletion.ker_evalₐ_eq_map_pow`
- theorem `AdicCompletion.exists_eq_algebraMap_add`
- theorem `AdicCompletion.isUnit_one_add_of_mem_map`
- theorem `AdicCompletion.isUnit_add_of_mem_map`
- theorem `AdicCompletion.isUnit_of_isUnit_algebraMap`
- theorem `AdicCompletion.isUnit_one_add_of_mem_map_maximalIdeal`
- theorem `AdicCompletion.maximalIdeal_fg`
- instance `AdicCompletion.instIsLocalRingMaximalIdeal`
- theorem `AdicCompletion.maximalIdeal_pow_eq_ker_evalₐ`
- theorem `AdicCompletion.maximalIdeal_eq_ker_evalₐ_one`
- theorem `AdicCompletion.mem_maximalIdeal_iff`
- def `AdicCompletion.quotientMaximalIdealPowAlgHom`
- theorem `AdicCompletion.quotientMaximalIdealPowAlgHom_mk`
- theorem `AdicCompletion.quotientMaximalIdealPowAlgHom_bijective`
- def `AdicCompletion.quotientMaximalIdealPowAlgEquiv`
- theorem `AdicCompletion.quotientMaximalIdealPowAlgEquiv_mk`
- theorem `AdicCompletion.quotientMaximalIdealPowAlgEquiv_mk_algebraMap`
- theorem `AdicCompletion.isUnit_algEquiv_iff`
- theorem `AdicCompletion.comap_maximalIdeal_algEquiv`
- theorem `AdicCompletion.map_maximalIdeal_algEquiv`
- theorem `AdicCompletion.maximalIdeal_eq_map_algEquiv`
- theorem `AdicCompletion.maximalIdeal_pow_eq_map_algEquiv`
- theorem `AdicCompletion.algEquiv_algebraMap_mem_maximalIdeal`
- def `AdicCompletion.quotientMaximalIdealPowAlgEquivOfAlgEquiv`
- theorem `AdicCompletion.quotientMaximalIdealPowAlgEquivOfAlgEquiv_mk`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib.RingTheory.AdicCompletion.Completeness`, `Mathlib.RingTheory.AdicCompletion.LocalRing`, `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`, `Mathlib.RingTheory.Ideal.Quotient.Operations`, `Mathlib.RingTheory.Noetherian.Defs`.
