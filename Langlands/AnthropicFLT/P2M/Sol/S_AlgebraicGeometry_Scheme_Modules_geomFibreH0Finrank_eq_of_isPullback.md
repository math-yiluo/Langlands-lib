# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry`: namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry` dropped.
- 3 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback`. Statement. `AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback`: if `A' ⟶ Spec S'` is the base change of
`X ⟶ Spec S` along `φ : S → S'` and `M'` is isomorphic to the pullback of `M`, then for every field `K` with
`sK : S' → K`, the dimension of the global sections on the geometric fibre of `M'` at `sK` equals that of
`M` at `sK ∘ φ`.

Proof. The fibre of `A'` over `Spec K` is canonically the fibre of `X` over `Spec K` via `sK ∘ φ` (pasting
pullback squares; `iUp`, `iDown`), under which the pullbacks of `M'` and `M` correspond; the induced
isomorphism of global sections (`restrictTopEquiv`) is `K`-linear for the algebra structures used in
`geomFibreH0Finrank`, so the dimensions agree.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry.Scheme.Modules.H0CartesianAux.map_map`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry.Scheme.Modules.H0CartesianAux.map_irrel`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry.Scheme.Modules.H0CartesianAux.mmap_mmap`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry.Scheme.Modules.H0CartesianAux.mmap_irrel`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry.Scheme.Modules.H0CartesianAux.image_top_of_isIso`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry.Scheme.Modules.H0CartesianAux.iUp`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry.Scheme.Modules.H0CartesianAux.iDown`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry.Scheme.Modules.H0CartesianAux.restrictTopEquiv`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry.Scheme.Modules.H0CartesianAux.restrictTopEquiv_smul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme` (same contribution).
Other imports: `Mathlib`.
