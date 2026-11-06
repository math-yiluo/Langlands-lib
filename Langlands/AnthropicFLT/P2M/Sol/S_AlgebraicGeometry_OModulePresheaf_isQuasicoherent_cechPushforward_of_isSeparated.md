# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated`.

Proof. Namespace `C2QC`: four restriction identities for FLT presheaves (`res_eq_zero_of_eq`, `res_via`,
`res_res_of_eq`, `res_smul'`). `solution` checks the two localisation conditions of quasi-coherence
(`isQuasicoherent_iff`) for an affine `U` of `P` and `f : Γ(P, U)`. The charts `K'.U i ∩ p⁻¹(U)` and their pairwise
intersections are affine (`fiberAffineOpen`, `isAffineOpen_inf_of_isSeparated`, using separatedness), and
with `g` the pullback of `f` to them, the charts over `D(f)` are the basic opens `D(g)` (`eD`, `eD2`). Extension:
for a cocycle `x` over `D(f)`, quasi-coherence of `G` on each chart gives `y i` with `y i = g^(n i) x i` on `D(g)`;
after raising to a common power `N` the differences `δ i j` of the `y' i` on the overlaps vanish on `D(g)`, so
a further power `g^M` kills them (quasi-coherence on the affine overlaps), and `z i = g^M y' i` is a cocycle
over `U` restricting to `f^(M+N) x`. Injectivity: if a cocycle over `U` restricts to `0` over `D(f)`, each
component is killed by a power of `g`, and the maximum of these powers works for all charts.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated.C2QC.res_eq_zero_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated.C2QC.res_via`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated.C2QC.res_res_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated.C2QC.res_smul'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution).
Other imports: `Mathlib`.
