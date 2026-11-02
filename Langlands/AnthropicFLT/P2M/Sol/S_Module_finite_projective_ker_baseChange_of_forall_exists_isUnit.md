# `Langlands.AnthropicFLT.P2M.Sol.S_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit`. Statement. `Module.finite_projective_ker_baseChange_of_forall_exists_isUnit`: let `δ : C₀ → C₁`, `Θ : F → C₀` be `R`-linear and
`A` an `R`-algebra. If every point of `Spec A` has a neighbourhood `D(g)` (`g ∈ R`) such that after every base change
inverting `g` the kernel of `δ` is finite projective of rank `r` and contained in the image of `Θ`, then the same holds
over `A`.

Proof. Finitely many of the `D(g)` cover `Spec A`. Kernels commute with the flat localizations `A → A_g`, so the
properties hold for the localizations of `ker (δ ⊗ A)`; finiteness, projectivity, rank and the containment
`ker ⊆ im` are local for Zariski covers.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech` (Library).
Other imports: `Mathlib`.
