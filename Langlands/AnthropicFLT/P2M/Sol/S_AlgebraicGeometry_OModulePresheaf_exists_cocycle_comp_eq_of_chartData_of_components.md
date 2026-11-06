# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components`.

Proof (direct). From the cocycle condition and bijectivity, `u i i = id` and `u j i ∘ u i j = id`; also
`θE ∘ ϑ = 0`. Extend the given maps `zC i j` (`i < j`) to all pairs by `Z i j = zC i j` for `i < j`,
`Z i j = −zC j i` for `i > j` and `Z i i = 0` (`Z_lt`, `Z_gt`, `Z_self`); `Z` is semilinear, compatible with
restriction and additive on triples, `Z i j + Z j l = Z i l` (`Z_smul`, `Z_nat`, `Z_cocy`, by case analysis on the
order using `hzCs`, `hzCn`, `hzCc`). Then define
`u'' i j = u i j − ϑ_j ∘ Z i j ∘ θE_i` and `θF'' i k = θF i k + lam k ∘ YC k i ∘ θE_i`. The properties of `u''`
(semilinearity, restriction, `ϑ`, `θE`, the cocycle condition) follow from those of `u` and of `Z`; `u''` is bijective
with inverse given by the same formula in the other direction. The properties of `θF''` follow from those of `θF`
and of `YC` (`hY`), and the compatibility `θF'' j ∘ u'' i j = θF'' i` follows from `ht` and `hzt` together with
`θF ∘ ϑ = lam`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library).
Other imports: `Mathlib`.
