# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback`

Ported by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Statement module (FLT `Theorems/`):
base change of a finite locally free quotient.

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.lean` (SHA-256
`ac98b5943a9b03a02d2c81776def1f9a2a3646e701ad5515ef52566403da6330`) from the Anthropic Lean
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
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.solution`
  (a tactic from `P2M.Util`) is replaced by the term
  `P2MW.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.solution hR hX hsq htq w'`,
  the companion solution theorem applied to the explicit arguments of the theorem. The
  theorem statement is unchanged.

## Content

`AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback`: let
`p : X ⟶ Y` be finite, flat, locally of finite presentation and surjective, and let
`s t : R ⟶ X` satisfy `IsPullback s t p p`, so `R = X ×_Y X`. Let `g : Y' ⟶ Y`, let
`X' = X ×_Y Y'` with projections `gX : X' ⟶ X` and `p' : X' ⟶ Y'` (`hX`), and let
`R' = R ×_X X'` along `s` with projections `gR` and `s'` (`hsq`). Let `t' : R' ⟶ X'`
satisfy `gR ≫ t = t' ≫ gX` and `s' ≫ p' = t' ≫ p'`. Then `p'` is finite, flat, locally
of finite presentation and surjective, `IsPullback s' t' p' p'` holds, and `p'` is a
coequalizer of `s'` and `t'` (`Nonempty (IsColimit (Cofork.ofπ p' w'))`). The proof term
applies the companion solution theorem.

## Declarations

- theorem `AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback`

## Dependencies

Ported FLT modules imported:
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback`.
All modules also import `Mathlib`.
