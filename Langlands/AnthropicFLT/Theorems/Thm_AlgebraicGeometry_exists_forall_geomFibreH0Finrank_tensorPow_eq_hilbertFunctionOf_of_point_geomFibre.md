# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre.solution S f 𝓛X hX₁ 𝔓 S' ψ Z ι j hj₁ hj₂ k sk P' m' q Zk ιk hιk e he₁ he₂ hZk`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 23 here); in 5 lines the replacements `Type` (universe 0) → `Type uz` (3 places), `Scheme.{0}` → `Scheme.{uz}` (3 places) are made, and these lines are otherwise unchanged. Consequently the theorem statement becomes universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre`: let `𝔓`
be a presentation of `𝓛X` on `X ⟶ Spec S`, `j` the base-changed embedding of `X ×_S Spec S'` into `ℙⁿ_{S'}`,
`Z ⊆ X ×_S Spec S'` closed, and `Z_k` the geometric fibre at `sk : S' → k` (`k` algebraically closed), embedded
in `ℙⁿ_k` compatibly, coming from a Hilbert point `q` with Hilbert function `hilbertFunctionOf n P' m'`. Then
for large `d` the dimension of `H⁰` of the geometric fibre of `Z` with the twists `(𝓛X|_Z)^{⊗d}` is
`hilbertFunctionOf n P' m' d`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre.solution`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above.

- theorem `AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre` (same contribution).
Other imports: none.
