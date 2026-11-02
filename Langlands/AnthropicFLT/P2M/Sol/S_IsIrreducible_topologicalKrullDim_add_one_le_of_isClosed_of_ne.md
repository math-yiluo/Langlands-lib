# `Langlands.AnthropicFLT.P2M.Sol.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne`. Statement. `IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne`: if `Y` is a proper closed subset of an irreducible
set `Z`, then `dim Y + 1 ≤ dim Z` (topological Krull dimension).

Proof. A chain of irreducible closed subsets of `Y` consists of irreducible closed subsets of `Z` contained in
`Y ⊊ Z`; appending `Z` gives a longer chain (local `push`, `push_strictMono`, `push_lt_top`, `main`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.P2mDim.topIC`
- def `P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.P2mDim.push`
- theorem `P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.P2mDim.push_strictMono`
- theorem `P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.P2mDim.coe_push_subset`
- theorem `P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.P2mDim.push_lt_top`
- theorem `P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.P2mDim.main`
- theorem `P2MW.S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
