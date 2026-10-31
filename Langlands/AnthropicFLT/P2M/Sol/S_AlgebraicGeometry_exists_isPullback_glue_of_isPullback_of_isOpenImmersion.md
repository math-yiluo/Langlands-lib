# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion`

Ported module of the proof submitted by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` (descent of schemes of finite presentation along finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate` command(s) (an FLT command from `P2M.Util` that re-activates scoped extensions) are removed; the file compiles without them.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `TwoOpenGlue`). `X₀` is the colimit of the wide span `U₀ ← W₀ → V₀`, which exists in
schemes because both legs are open immersions; the colimit inclusions `iU`, `iV` are open immersions,
cover `X₀`, and form a pullback square with `a`, `b` (`isPullback_charts`). The structure map `f₀` is the
induced map from `u₀` and `v₀`. Local finite presentation and quasi-compactness of `f₀` are checked on
the two-chart cover; quasi-separatedness uses an analysis of the diagonal on the charts
(`TwoOpenGlue.QSGlue`, using that `a ≫ u₀` is quasi-compact). The morphism `π` is glued from
`πU ≫ iU` and `πV ≫ iV` on the cover `{U, V}` of `X` (`Scheme.Cover.glueMorphisms`); the preimages of the
charts of `X₀` under `π` are `U` and `V` (`preimage_π_iU`, `preimage_π_iV`), so the chart squares are
pullbacks (`sqU`, `sqV`). Finally `Scheme.isPullback_of_openCover` reduces the global pullback property
to the two charts, where it is the given squares for `U` and `V`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.F`
- instance `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.F_map_isOpenImmersion`
- def `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.X₀`
- def `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.iU`
- def `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.iV`
- def `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.i0`
- scoped unnamed instance `instance : IsOpenImmersion (iU ia ib)`
- scoped unnamed instance `instance : IsOpenImmersion (iV ia ib)`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.ia_iU`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.ib_iV`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.ia_iU_eq_ib_iV`
- def `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.f₀`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.iU_f₀`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.iV_f₀`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.cover`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.range_union`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.preimage_iV_iU`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.isPullback_charts`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.lfp`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.qc`
- abbrev `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.QSGlue.δ`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.QSGlue.quasiCompact_δ_self`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.QSGlue.quasiCompact_δ_of_isPullback`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.QSGlue.quasiCompact_δ_symm`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.QSGlue.quasiSeparated_glue`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.qs`
- def `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.coverX`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.kU_kV_compat`
- def `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.π`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.jU_π`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.jV_π`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.π_f₀`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.preimage_π_iU`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.preimage_π_iV`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.sqU`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.sqV`
- def `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.TwoOpenGlue.coverX₀`
- theorem `P2MW.S_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion.solution`

## Dependencies

Ported FLT modules imported: none.
All modules also import `Mathlib`.
