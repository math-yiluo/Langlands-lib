# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 3 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.MvPolynomial _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry _root_.HomogeneousLocalization`: namespace `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry` dropped.
- 3 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names. The command `export _root_.AlgebraicGeometry.ProjSpace.BCComap (map_mem)` is dropped; see the port edit below.
- Port edit replacing a `P2M.Util` alias (FLT line 169, line 180 here): `dh n i e ⟨φ (G : MvPolynomial (Fin (n + 1)) A), map_mem n A B e G⟩ := by` is replaced by `dh n i e ⟨φ (G : MvPolynomial (Fin (n + 1)) A), _root_.AlgebraicGeometry.ProjSpace.BCComap.map_mem n A B e G⟩ := by`. FLT `p2m_export "AlgebraicGeometry.ProjSpace.BCComap" "map_mem"` aliases the private declaration(s) `_root_.AlgebraicGeometry.ProjSpace.BCComap.`, `_root_.map_mem.` (declared earlier in the file) into the current namespace. Standard `export` cannot do this: `AlgebraicGeometry.ProjSpace.BCComap` contains only private declarations and is not a registered namespace (`unknown namespace`). The command is dropped, and the uses of the alias are written with the full name of the private declaration, which denotes the same declaration.
- Port edit replacing a `P2M.Util` alias (FLT line 177, line 188 here): `num := ⟨φ (G : MvPolynomial (Fin (n + 1)) A), map_mem n A B e G⟩` is replaced by `num := ⟨φ (G : MvPolynomial (Fin (n + 1)) A), _root_.AlgebraicGeometry.ProjSpace.BCComap.map_mem n A B e G⟩`. FLT `p2m_export "AlgebraicGeometry.ProjSpace.BCComap" "map_mem"` aliases the private declaration(s) `_root_.AlgebraicGeometry.ProjSpace.BCComap.`, `_root_.map_mem.` (declared earlier in the file) into the current namespace. Standard `export` cannot do this: `AlgebraicGeometry.ProjSpace.BCComap` contains only private declarations and is not a registered namespace (`unknown namespace`). The command is dropped, and the uses of the alias are written with the full name of the private declaration, which denotes the same declaration.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 17 here); in 3 lines the replacements `Type` (universe 0) → `Type uz` (3 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span`. Statement. `AlgebraicGeometry.ProjSpace.eq_comap_map_of_ideal_basicOpen_eq_span`: let `B` be an `A`-algebra, `I` a
homogeneous ideal of `A[X₀, …, Xₙ]`, `𝓘` the ideal sheaf on `ℙⁿ_A` with chart ideals generated by the
dehomogenizations of `I`, and `𝓙` the analogous ideal sheaf on `ℙⁿ_B` for the extended ideal `I B`.
Then `𝓙` is the pullback of `𝓘` along `ProjSpace.map A B n : ℙⁿ_B ⟶ ℙⁿ_A`.

Proof (namespace `AlgebraicGeometry.ProjSpace.BCComap`). Section `Dehom`: the dehomogenization map `dh`
on forms of each degree (additive, multiplicative, compatible with sums and homogeneous components),
and `dh_decompose_mem_of_mem_span`. Section `Map`: homogeneous components commute with
`MvPolynomial.map`, the preimage of a chart under `ProjSpace.map` is the corresponding chart
(`basicOpen_le_preimage`), and the map on sections sends `F / Xᵢ^e` to `F_B / Xᵢ^e` (`appLE_dh`). Both
ideal sheaves are determined by their ideals on the standard charts, which cover (ideal sheaf
extensionality `IdealSheafData.ext_of_iSup_eq_top`); on each chart both ideals are generated by the
dehomogenized images of the forms of `I`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.X_pow_mem`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.dh`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.dh_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.dh_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.dh_congr`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.dh_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.dh_mul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.dh_mul'`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.dh_sum`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.coe_decompose`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.decompose_sum_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.dh_decompose_mem_of_mem_span`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.decompose_of_isHomogeneous`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.homogeneousComponent_map`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.coe_decompose_map`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.basicOpen_le_preimage`
- private theorem `AlgebraicGeometry.ProjSpace.BCComap.map_mem`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.AlgebraicGeometry.ProjSpace.BCComap.appLE_dh`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le` (same contribution).
Other imports: `Mathlib`.
