# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation`

Ported by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Proof module (FLT `P2M/Sol/`) of
Stacks Proposition 66.14.1 (Tag 07S6) when every equivalence class lies in an affine open,
adapted to use published Library results for its two affine-case inputs.

## Source and licence

Adapted port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.lean` (SHA-256
`a4c6aa3040e1baa2711d768197a89ff2c14866f6343d9a82f9bf25ca5a84cde8`) from the Anthropic Lean
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
  Its one `p2m_reactivate "N"` command (it re-activates the scoped extensions, here the
  scoped instances of section `restrict`, of the namespace `N`) is replaced by
  `open scoped _root_.N` with the same namespace, which activates the same scoped
  extensions.
- The FLT file imports `Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`;
  the port imports its port
  `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`.
- The FLT file imports two FLT statement modules that are not ported here. They are
  replaced by published Library modules with the same mathematical content:
  - FLT `Theorems.Thm_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation`
    (the affine case, Stacks Proposition 39.23.9, Tag 03BM) is replaced by
    `Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationAffineQuotientProof`. In
    the proof of `main`, the call to
    `AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation`
    is replaced by a call to the Library theorem
    `Langlands.AlgebraicGeometry.FiniteLocallyFreeQuotient.existsAffineQuotient`, which has
    the same hypotheses, the same arguments and the same conclusion.
  - FLT `Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation`
    (one point; Stacks Lemma 39.24.1, Tag 03JE) is replaced by the Library port
    `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`
    (the same lemma for a finite set of points). In the proof of
    `exists_invariant_affine_cover`, the one-point theorem applied to `hU x` and `hxU x` is
    replaced by the finite-set theorem applied to the singleton `{x}`
    (`Set.finite_singleton x`), to `hU x`, and to the hypothesis for `{x}` obtained from
    `hxU x`; membership `x ∈ W x` is read off from `Set.mem_singleton x`. The statement of
    `exists_invariant_affine_cover` is unchanged.
- No other change: the other declarations, statements and proofs are the FLT text. With the
  project Mathlib it compiles without errors; the `haveI` style linter warns four times.

## Content

All declarations except `solution` are in namespace `Q1SCH`.

- `exists_invariant_affine_cover`: under `hequiv` and `haff`, and for `s`, `t` finite, flat
  and locally of finite presentation, every point `x` has an affine open `W x ∋ x` with
  `s⁻¹(W x) = t⁻¹(W x)`. It applies the finite-set invariant affine open theorem to `{x}`.
- Section `restrict`: for an open `W` with `s⁻¹W = t⁻¹W`, `sW` and `tW` are the
  restrictions of `s` and `t` to `s⁻¹W ⟶ W`. They are pullbacks of `s` and `t`
  (`isPullback_sW`, `isPullback_tW`), hence finite, flat and locally of finite presentation
  (three scoped instances for `sW`; `tW_finite`, `tW_flat`, `tW_lfp`). The restricted pair
  is again jointly monic (`mono_restrict`) and an equivalence relation
  (`equivalence_restrict`, through `rel_restrict_iff`, which lifts a related pair of maps
  into `W` along the open immersion `s⁻¹W ⟶ R`).
- `main`: chooses the invariant affine cover `W`, applies the Library affine quotient
  theorem `existsAffineQuotient` to each restricted pair over the affine `W x`, and glues
  the results with the ported theorem
  `AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict`.
- `solution` restates `main`.

This follows the proof of Stacks Proposition 66.14.1 (Tag 07S6): cover `X` by `R`-invariant
affine opens (Groupoids Lemma 39.24.1, Tag 03JE), take the affine quotients (Groupoids
Proposition 39.23.9, Tag 03BM) and glue.

## Declarations

Names, namespaces and statements are the FLT ones. All declarations are in the FLT namespace
`P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.Q1SCH`,
except `solution`, which is in
`P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation`.

- theorem `exists_invariant_affine_cover`
- def `sW`, `tW`
- theorem `sW_ι`, `tW_ι`, `isPullback_sW`, `isPullback_tW`, `tW_finite`, `tW_flat`, `tW_lfp`,
  `mono_restrict`, `rel_restrict_iff`, `equivalence_restrict`
- three anonymous scoped instances (`IsFinite`, `Flat`, `LocallyOfFinitePresentation` of `sW`)
- theorem `main`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.solution`

## Dependencies

Library modules imported:

- `Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationAffineQuotientProof`
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`
  (ported with this module)

All modules also import `Mathlib`.
