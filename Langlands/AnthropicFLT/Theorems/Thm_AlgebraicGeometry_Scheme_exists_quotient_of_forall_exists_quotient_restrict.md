# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`

Ported by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Statement module (FLT `Theorems/`):
gluing local quotients over an invariant open cover.

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean` (SHA-256
`e6e8efc87fc366f1d87d4f4e48032ee39ca415cde406b48778cbaa68c286c536`) from the Anthropic Lean
formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`;
project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at
6e837e75355538c7f80bab5b956861e86c4eacc2", literature id
`anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the
changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT
`LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; the Mathlib
  import is unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.solution`
  (a tactic from `P2M.Util`) is replaced by the term
  `P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.solution s t W hxW hinv loc`,
  the companion solution theorem applied to the explicit arguments of the theorem. The
  theorem statement is unchanged.

## Content

`AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict`: let
`s t : R ⟶ X` be morphisms of schemes and `W : X → X.Opens` a family of opens with
`x ∈ W x` and `s⁻¹(W x) = t⁻¹(W x)` for every point `x`. Suppose that for each `x` the
restricted pair `s|_{W x}`, `t|_{W x}` (the latter transported along the equality
`s⁻¹(W x) = t⁻¹(W x)`) has a quotient: a finite, flat, locally finitely presented,
surjective `p : W x ⟶ Y` equalizing them with `IsPullback (s|_{W x}) (t|_{W x}) p p`. Then
there are `Y` and `p : X ⟶ Y` with `s ≫ p = t ≫ p`, `p` finite, flat, locally of finite
presentation and surjective, `IsPullback s t p p`, and `p` a coequalizer of `s` and `t`.
No hypothesis on `s` and `t` themselves is needed. The proof term applies the companion
solution theorem.

## Declarations

- theorem `AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict`

## Dependencies

Ported FLT modules imported:
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`.
All modules also import `Mathlib`.
