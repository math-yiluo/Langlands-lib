# `Langlands.AnthropicFLT.Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated.solution R K f t`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

For a domain `R` with fraction field `K`, `f : X ⟶ Spec R` separated and `t : T ⟶ Spec R` flat,
restriction to generic fibres of morphisms `T ⟶ X` over `Spec R` is injective.
The proof term applies the companion solution theorem.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated` (same contribution).
Other imports: `Mathlib`.
