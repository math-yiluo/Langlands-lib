# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isCompact_inter_setOf_isIso_fibre_of_isAffineOpen_of_isProper_of_flat`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_isCompact_inter_setOf_isIso_fibre_of_isAffineOpen_of_isProper_of_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 17 here); in 1 line the replacements `Scheme.{0}` → `Scheme.{uz}` (1 place) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_isCompact_inter_setOf_isIso_fibre_of_isAffineOpen_of_isProper_of_flat.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isCompact_inter_setOf_isIso_fibre_of_isAffineOpen_of_isProper_of_flat`. Statement. `AlgebraicGeometry.isCompact_inter_setOf_isIso_fibre_of_isAffineOpen_of_isProper_of_flat`: for proper, flat,
finitely presented `p : Z ⟶ Y`, `q : X ⟶ Y` and `h : Z ⟶ X` over `Y`, and an affine open `V ⊆ Y`, the set of points
of `V` at which the map of fibres `h_y` is an isomorphism is compact.

Proof (noetherian approximation). Restrict to `V = Spec A`. By the ported
`exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation` the data
descend to a finitely generated subring `T ⊆ A`, a noetherian ring. The iso-fibre locus over `Spec T` is open
(ported `exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat`), hence compact as
`Spec T` is noetherian, and the locus over `Spec A` is its preimage under the affine map `Spec A ⟶ Spec T` (ported
`isIso_fibre_iff_isIso_fibre_of_isPullback_of_isPullback`), which is again compact.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_isCompact_inter_setOf_isIso_fibre_of_isAffineOpen_of_isProper_of_flat.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isIso_fibre_iff_isIso_fibre_of_isPullback_of_isPullback` (same contribution).
Other imports: `Mathlib`.
