# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 24 here); in 73 lines the replacements `Type` (universe 0) → `Type uz` (46 places), `Scheme.{0}` → `Scheme.{uz}` (35 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq`. Statement. `AlgebraicGeometry.exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq`: let `f : X ⟶
Spec S` be flat and locally of finite presentation, with an invertible `𝓛X` giving a closed immersion by sections.
Suppose that for every `P : ℚ[X]` there are `C P ⟶ Spec S` and natural assignments `ptC P` sending flat, finitely
presented closed subschemes `Z ⊆ X ×_S Spec S'` with Hilbert polynomial `P` (on every geometric fibre, with respect
to `𝓛X`) to `S`-points of `C P`. Then there is a natural assignment `pt` sending every flat, finitely presented
closed subscheme `Z` to an `S`-point of the coproduct `∐ C`, which equals `ptC P ≫ Sigma.ι C P` whenever `Z` has
Hilbert polynomial `P`.

Proof. Section `BaseChange` sets up base change of families and of the twisted line bundles (`bcMap`, `powIso`,
`hF_baseChange`). Section `Pieces`: by the ported
`exists_cover_forall_geomFibreH0Finrank_tensorPow_eq_eval_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`
the Hilbert polynomial of `Z` is constant on the members `D(r_j)` of a finite cover of `Spec S'`, so `Spec S'` is
the disjoint union of the opens `U P` of points with Hilbert polynomial `P` (`disjoint_U`, `iSup_U`, `isClosed_U`,
`isAffineOpen_U`; the dimension is computed after base change by the ported
`Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback`). Section `Rings`/`Main`: the restriction of `Z` over each
`U P` has Hilbert polynomial `P` (`res_hasHP`) and `ptC P` gives a point of `C P`; these are glued into a
morphism to `∐ C` by the ported `Scheme.existsUnique_hom_sigma_of_disjoint_iSup_eq_top` (`ptHom`). Section
`Clauses`: naturality (`pt_nat`) follows from the uniqueness of glued morphisms and the naturality of `ptC`, and
the comparison with `ptC P` (`pt_const`) from the ported
`Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.bcMap`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.isPullback_bcMap`
- abbrev `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.pow`
- abbrev `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.hF`
- def `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.powIso`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.hF_baseChange`
- abbrev `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Res`
- abbrev `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.resι`
- abbrev `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.resE`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.res_comm`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.res_isPullback`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.res_props`
- structure `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Datum`
- def `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Datum.Computes`
- def `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Datum.U`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Datum.basicOpen_le_U`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Datum.exists_mem_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Datum.iSup_U`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.poly_eq_of_eventually_eq`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.exists_geomPoint`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Datum.eventually_eq_of_mem_U`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Datum.mem_U_of_eventually_eq`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Datum.disjoint_U`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Datum.isClosed_U`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Datum.isAffineOpen_U`
- def `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.resHom`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.specMap_resHom`
- structure `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Sub`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.exists_datum`
- def `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.datum`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.datum_computes`
- def `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.Sub.res`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.res_hasHP`
- def `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.v`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.existsUnique_ptHom`
- def `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.ptHom`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.ptHom_spec`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.ptHom_unique`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.ptHom_over`
- def `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.pt`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.isoSpec_hom_specMap_appLE`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.U_baseChange`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.pt_const`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.H1PT.pt_nat`
- theorem `P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_cover_forall_geomFibreH0Finrank_tensorPow_eq_eval_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation` (same contribution).
Other imports: none.
