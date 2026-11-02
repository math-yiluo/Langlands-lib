# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization: The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. The FLT lemma is stated for coproducts indexed by `σ : Type u` of schemes in universe `u`. The Hilbert scheme is a coproduct over `Polynomial ℚ : Type` of schemes in universe `uz`, so the index type is generalized to `σ : Type*` with `[Small.{u} σ]` (such coproducts exist in `Scheme.{u}`). This generalizes the statement: for `σ : Type u` the instance `Small.{u} σ` holds, giving the FLT statement. The proof is unchanged. The changed lines are:
  - line 22 here:
    FLT text (universe-0 port):

    ```lean
        {σ : Type u} (X : σ → Scheme.{u}) {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    ```

    replacement:

    ```lean
        {σ : Type*} [Small.{u} σ] (X : σ → Scheme.{u}) {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated`. Statement. `AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated`: for a small family of separated morphisms
`f i : X i ⟶ Y`, the induced morphism `∐ X ⟶ Y` is separated.

Proof. The diagonal of `∐ X ⟶ Y` is the disjoint union of the diagonals of the `f i` followed by the inclusion of
the open and closed pieces `X i ×_Y X i` into `(∐ X) ×_Y (∐ X)`; hence it is a closed immersion.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
