# `Langlands.AnthropicFLT.Theorems.Thm_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit`

Ported for task `c23cb2c8-d7bd-4f3b-904d-448ce5a3c826` (proof of `Langlands.GroupScheme.AffineHomImageStatement`), as part of the FLT closure of `HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem`. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit.solution K hΔ hS hnil`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `HopfAlgebra.free_subalgebra_of_isNilpotent_ker_counit K hΔ hS hnil`: let `H` be a commutative Hopf
algebra over a field `k` (in universes `v` and `u`) and `K` a `k`-subalgebra of `H` such that `Δ x` lies in the
`k`-span of `{a ⊗ b | a ∈ K, b ∈ K}` for every `x ∈ K` (`hΔ`) and `K` is stable under the antipode (`hS`). If the
kernel of the counit restricted to `K`, `RingHom.ker ((Bialgebra.counitAlgHom k H).comp K.val)`, is a nilpotent
ideal of `K` (`hnil`), then `H` is a free `K`-module: `Module.Free ↥K H`.

This is the infinitesimal case of the faithful flatness of a commutative Hopf algebra over a Hopf subalgebra.
Compare J. S. Milne, *Algebraic Groups* (Cambridge University Press 2017; project copy: the 2022 corrected reprint),
proof of Theorem 3.31, which first treats the case where the augmentation ideal of the subalgebra is nilpotent, with
the same conclusion that lifts of a basis of `B ⧸ I_A B` form a basis of `B` over `A`. The FLT proof of that step
differs from Milne's: it uses the torsor isomorphism
`HopfAlgebra.exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span` instead of Milne's snake-lemma
diagram.

The proof term applies the companion solution theorem `P2MW.S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `HopfAlgebra.free_subalgebra_of_isNilpotent_ker_counit`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit` (same contribution).
Other imports: `Mathlib`.
