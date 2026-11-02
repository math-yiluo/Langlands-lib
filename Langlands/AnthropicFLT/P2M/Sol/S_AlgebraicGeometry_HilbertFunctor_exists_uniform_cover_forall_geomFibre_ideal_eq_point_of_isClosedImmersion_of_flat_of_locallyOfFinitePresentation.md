# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 20 here); in 6 lines the replacements `Type` (universe 0) → `Type uz` (3 places), `Scheme.{0}` → `Scheme.{uz}` (3 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`:
there is a function `D₀ : ℚ[X] → ℕ` such that for every ring `A` and every closed subscheme
`ι : Z ⟶ ℙⁿ_A`, flat and locally of finite presentation over `Spec A`, there is a finite cover of
`Spec A` by basic opens `D(r_j)` with Hilbert polynomials `P_j` such that for every `m ≥ D₀ P_j` and
every geometric point `A → k` with `r_j` invertible, the geometric fibre `Z_k ⊆ ℙⁿ_k` (a pullback
square) comes from a point `q` over `k` with Hilbert function `hilbertFunctionOf n P_j m`, in the
sense that the forms of degree `≥ m` in `q.I` are exactly those vanishing on `Z_k`.

Proof. Let `D₀ P` be the uniform regularity bound of the ported
`HilbertFunctor.exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq`.
Take the cover and polynomials from
`HilbertFunctor.exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`.
For a geometric point, let `Z_k` be the pullback of `ι` along `ProjSpace.map A k n` and `I` its
homogeneous ideal (`HilbertFunctor.exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial`);
its Hilbert function eventually equals `P_j`, hence equals `P_j` from `D₀ P_j` on, and
`HilbertFunctor.exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq` gives `q`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq` (same contribution).
Other imports: none.
