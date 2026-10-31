# `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit`

Ported for task `8836e68b-90ba-4f01-a129-026ad9adfa9d` (descent of smoothness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `AlgHomSpreadUnique`, which repeats the direct-limit lemmas of the algebra-map module:
`limEquiv`, `Φ`, `exists_stepT_eq_zero`, `exists_common_kill`). Choose finitely many generators of `A`
(`Algebra.FiniteType.iff_quotient_mvPolynomial''`). The differences `φ₁ (1 ⊗ aₖ) - φ₂ (1 ⊗ aₖ)` map to `0`
in `R ⊗[R₀] B`, so they all vanish at a common later stage `j`. After composing with the map to stage `j`,
the two maps agree on `G i ⊗ 1` (both are `G i`-algebra maps) and on the generators, hence everywhere
(`Algebra.TensorProduct.ext`, `MvPolynomial.algHom_ext`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.F`
- scoped instance `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.directedSystem_F`
- abbrev `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.toR`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.toR_apply`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.toR_f`
- def `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.limToR`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.limToR_of`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.limToR_bijective`
- def `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.limEquiv`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.limEquiv_symm_algebraMap`
- abbrev `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.mapT`
- abbrev `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.stepT`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.mapT_eq_rTensor`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.stepT_eq_rTensor`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.mapT_stepT`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.stepT_stepT`
- def `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.Φ`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.Φ_mapT`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.exists_mapT_eq`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.exists_stepT_eq_zero`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.exists_common_lift`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.exists_common_kill`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.AlgHomSpreadUnique.exists_apply_eq`
- theorem `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit` (Library, ported by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`).
All modules also import `Mathlib`.
