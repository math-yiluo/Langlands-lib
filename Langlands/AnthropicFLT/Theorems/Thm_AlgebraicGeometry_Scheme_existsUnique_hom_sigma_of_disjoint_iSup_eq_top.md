# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top.solution H U hdisj hcov v`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- Universe generalization: The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. The FLT lemma is stated for coproducts indexed by `σ : Type u` of schemes in universe `u`. The Hilbert scheme is a coproduct over `Polynomial ℚ : Type` of schemes in universe `uz`, so the index type is generalized to `σ : Type*` with `[Small.{u} σ]` (such coproducts exist in `Scheme.{u}`). This generalizes the statement: for `σ : Type u` the instance `Small.{u} σ` holds, giving the FLT statement. The changed lines are:
  - line 22 here:
    FLT text (universe-0 port):

    ```lean
        {σ : Type u} (H : σ → Scheme.{u}) {T : Scheme.{u}} (U : σ → T.Opens)
    ```

    replacement:

    ```lean
        {σ : Type*} [Small.{u} σ] (H : σ → Scheme.{u}) {T : Scheme.{u}} (U : σ → T.Opens)
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.Scheme.existsUnique_hom_sigma_of_disjoint_iSup_eq_top`: let `(Hᵢ)` be a family of schemes
indexed by a `u`-small type `σ` (any universe) and `(Uᵢ)` pairwise disjoint opens covering `T`. Morphisms
`vᵢ : Uᵢ ⟶ Hᵢ` glue to a unique morphism `T ⟶ ∐ Hᵢ` restricting to `vᵢ` followed by the coproduct inclusion on
each `Uᵢ`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top.solution`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above.

- theorem `AlgebraicGeometry.Scheme.existsUnique_hom_sigma_of_disjoint_iSup_eq_top`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top` (same contribution).
Other imports: `Mathlib`.
