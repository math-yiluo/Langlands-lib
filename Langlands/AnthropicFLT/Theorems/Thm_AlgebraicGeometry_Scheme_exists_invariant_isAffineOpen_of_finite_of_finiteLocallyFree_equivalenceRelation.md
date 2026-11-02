# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`

Ported for task `22877948-227b-4ad5-bdb3-e13f5ea18c3d` (separated commutative group algebraic
spaces over a field are schemes). Statement module (FLT `Theorems/`) of finite-set Stacks
Lemma 39.24.1 (Tag 03JE).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation.lean` (SHA-256
`8234f584b38c9ef40cf59eb8e5f8aba0d88ebafb2a8d2051fb97e508926fdeaf`) from the Anthropic Lean
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
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation.solution` (a tactic from `P2M.Util`) is
  replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation.solution` applied to the explicit arguments of the theorem. The
  theorem statement is unchanged.

## Content

`AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`:
let `s t : R ⟶ X` be finite, flat and locally of finite presentation, such that for every
scheme `T` the relation "`x = φ ≫ s` and `y = φ ≫ t` for some `φ : T ⟶ R`" is an equivalence
relation on `T ⟶ X`. Let `S` be a finite set of points and `U` an affine open such that
`t r ∈ U` whenever `s r ∈ S`. Then there is an affine open `W ⊆ U` containing `S` with
`s⁻¹ W = t⁻¹ W`. The proof term applies the companion solution theorem.

## Declarations

- theorem `AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`.
All modules also import `Mathlib`.
