# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback`

Ported by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Proof module (FLT `P2M/Sol/`): base
change of a finite locally free quotient.

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.lean` (SHA-256
`ab4522b04488e28eef4c60c03de3631046bece499faa5436cbd2c9878446c80c`) from the Anthropic Lean
formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`;
project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at
6e837e75355538c7f80bab5b956861e86c4eacc2", literature id
`anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the
changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT
`LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
  The file uses none of its commands.
- No other change: the declaration, statement and proof are the FLT text. It compiles with
  the project Mathlib without errors.

## Content

`solution` has the hypotheses of the statement module: `p : X ⟶ Y` finite, flat, locally of
finite presentation and surjective with `IsPullback s t p p`, a base change `g : Y' ⟶ Y`
giving `p' : X' ⟶ Y'` and `gX : X' ⟶ X` (`hX`), the pullback `R'` of `s` along `gX` with
projections `gR` and `s'` (`hsq`), and `t'` with `gR ≫ t = t' ≫ gX` and
`s' ≫ p' = t' ≫ p'`.

- The four morphism properties of `p'` are stable under base change
  (`MorphismProperty.of_isPullback`).
- `IsPullback s' t' p' p'` is checked directly on the universal property. A cone `(a, b)`
  over `p'`, `p'` gives the cone `(a ≫ gX, b ≫ gX)` over `p`, `p`, hence a map to `R`
  through `hR`, and with `a` a map to `R'` through `hsq`. Uniqueness uses the uniqueness
  in `hsq`, `hR` and `hX`.
- The coequalizer property follows since `p'` is an effective epimorphism (Mathlib: a
  quasi-compact, flat, surjective morphism is one), so it is the coequalizer of its kernel
  pair `(s', t')` (`IsKernelPair.toCoequalizer`).

## Declarations

- theorem `P2MW.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.solution`

## Dependencies

Imports only `Mathlib`.
