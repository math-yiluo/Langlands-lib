# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq`

Ported module of the proof submitted by task `e36ae7da-512e-4a4d-a902-71146c92ec82` (descent of properness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions) are replaced by `open` commands with the same namespaces (written `_root_.N` where the name would otherwise resolve inside the current namespace). Exception: the first one, `p2m_open "MvPolynomial HomogeneousLocalization AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.AlgebraicGeometry"`, becomes `open MvPolynomial HomogeneousLocalization AlgebraicGeometry`: its last namespace does not exist yet at that point (the next command creates it), `open` rejects it, and the file compiles without it.
- 2 `p2m_export "N" "x y …"` command(s) (an FLT command from `P2M.Util` that adds, in the current namespace, aliases of the listed declarations of namespace `N`) are replaced by `export _root_.N (x y …)`, which adds the same aliases.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `AlgebraicGeometry.ProjSpace.ChartLift` inside the solution namespace). The evaluation
`MvPolynomial.aeval b` sends `X i` to `b i = 1`, a unit, so it extends to the localisation at `X i`
(`lift0`, `IsLocalization.Away.lift`); restricting to the degree-zero part gives an `R`-algebra map
(`liftAway`), and it sends `X k / X i` to `b k / b i = b k` (`liftAway_ratio`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.AlgebraicGeometry.ProjSpace.ChartLift.lift0`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.AlgebraicGeometry.ProjSpace.ChartLift.lift0_algebraMap`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.AlgebraicGeometry.ProjSpace.ChartLift.liftAway`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.AlgebraicGeometry.ProjSpace.ChartLift.liftAway_ratio`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.AlgebraicGeometry.ProjSpace.ChartLift.exists_algHom`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (published with the FLT port of task `69435287-9f1e-4abd-8483-5e65ff23668a`).
All modules also import `Mathlib`.
