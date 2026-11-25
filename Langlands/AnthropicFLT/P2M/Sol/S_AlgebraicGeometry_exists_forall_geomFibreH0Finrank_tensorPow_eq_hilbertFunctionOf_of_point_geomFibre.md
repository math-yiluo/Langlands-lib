# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre`

Ported for the proof of projective representability of the relative endomorphism functor of a projective abelian scheme. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 27 here); in 5 lines the replacements `Type` (universe 0) → `Type uz` (3 places), `Scheme.{0}` → `Scheme.{uz}` (3 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above and the renames described under “Names changed by the Library” below, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre`. Statement. `AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre`: let `𝔓`
be a presentation of `𝓛X` on `X ⟶ Spec S`, `j` the base-changed embedding of `X ×_S Spec S'` into `ℙⁿ_{S'}`,
`Z ⊆ X ×_S Spec S'` closed, and `Z_k` the geometric fibre at `sk : S' → k` (`k` algebraically closed), embedded
in `ℙⁿ_k` compatibly, coming from a Hilbert point `q` with Hilbert function `hilbertFunctionOf n P' m'`. Then
for large `d` the dimension of `H⁰` of the geometric fibre of `Z` with the twists `(𝓛X|_Z)^{⊗d}` is
`hilbertFunctionOf n P' m' d`.

Proof. Pull back `𝔓` to `Z_k` (ported `Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq`):
the pullback of `𝓛X` to `Z_k` is `𝒪(1)` for the embedding `ιk` (charts compatible by the ported
`ProjSpace.map_preimage_basicOpen_X` and `ProjSpace.restrictFun_app_app_awayToSection_eq_app_awayToSection_map`).
The dimension on the geometric fibre of `Z` equals the one computed on `Z_k` (ported
`Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback`), and on `Z_k` it is the Hilbert function by the ported
`HilbertFunctor.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre.F3Sol.smul_map_eq_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre.F3Sol.descend`
- def `P2MW.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre.F3Sol.powIso`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (ported with this file), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (ported with this file), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme` (ported with this file), `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (ported with this file), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq` (ported with this file), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point` (ported with this file), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback` (ported with this file), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_restrictFun_app_app_awayToSection_eq_app_awayToSection_map` (ported with this file).
Other imports: none.

## Names changed by the Library (22 November 2026)

weil-conjectures, on which the Library depends, declares 21 of the names of this extract itself, so that no module could import both. The Library renamed these 21 declarations: each keeps its name space and the last component of its name gets the marker `FLT` (`tensorPow` becomes `tensorPowFLT`, `tensorPow_zero` becomes `tensorPowFLT_zero`). In this file:

- its uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`, `AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero`, `AlgebraicGeometry.Scheme.Modules.tensorPow_succ`, `AlgebraicGeometry.Scheme.Modules.tensorPow_zero` are uses of `IsInvertibleFLT`, `pullbackFLT`, `tensorPowSectionFLT_zero`, `tensorPowFLT_succ`, `tensorPowFLT_zero` now;
- applications in dot notation on a hypothesis `h : Scheme.Modules.IsInvertibleFLT L` of lemmas of the name space `Scheme.Modules.IsInvertible` are written out (`h.pullback f` becomes `Scheme.Modules.IsInvertible.pullbackFLT (hL := h) f`): dot notation looks in the name space `IsInvertibleFLT`, and these lemmas stay in `IsInvertible`; the argument filled is the one dot notation filled.

Statements and proofs are otherwise unchanged. Elsewhere on this page the names are given as they now are.
