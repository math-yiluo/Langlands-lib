# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation`

Ported by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Statement module (FLT `Theorems/`) of
Stacks Proposition 66.14.1 (Tag 07S6) when every equivalence class lies in an affine open.

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.lean` (SHA-256
`0a8ac7573d0061ca65583e59379c03e51fd821c2f98f2dc41ed0313eaeadddf6`) from the Anthropic Lean
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
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.solution`
  (a tactic from `P2M.Util`) is replaced by the term
  `P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.solution s t hmono hequiv haff`,
  the companion solution theorem applied to the explicit arguments of the theorem. The
  theorem statement is unchanged.

## Content

`AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation`: let
`s t : R ⟶ X` be finite, flat and locally of finite presentation. Assume

- `hmono`: two maps `a b : T ⟶ R` with `a ≫ s = b ≫ s` and `a ≫ t = b ≫ t` are equal, so
  `(s, t)` is a monomorphism;
- `hequiv`: for every scheme `T`, the relation "`x = φ ≫ s` and `y = φ ≫ t` for some
  `φ : T ⟶ R`" is an equivalence relation on `T ⟶ X`;
- `haff`: for every point `x`, some affine open `U` contains `t r` for every `r` with
  `s r = x`, that is, the equivalence class `t(s⁻¹{x})` lies in an affine open.

Then there are a scheme `Y` and `p : X ⟶ Y` with `s ≫ p = t ≫ p`, `p` finite, flat,
locally of finite presentation and surjective, `IsPullback s t p p` (so `R = X ×_Y X`),
and `p` a coequalizer of `s` and `t`. This is Stacks Proposition 66.14.1 (Tag 07S6) when
the set `E` of its footnote 1 is all of `X`, without the base scheme. The proof term
applies the companion solution theorem.

## Declarations

- theorem `AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation`

## Dependencies

Ported FLT modules imported:
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation`.
All modules also import `Mathlib`.
