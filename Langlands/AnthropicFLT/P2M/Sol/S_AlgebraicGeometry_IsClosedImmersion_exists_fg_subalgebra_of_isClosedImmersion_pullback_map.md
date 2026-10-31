# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map`

Ported module of the proof submitted by task `8b63dc1d-84d3-43fa-a1d5-9657a89c8df1` (descent of separatedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

Proof (namespace `CIDescGC6`). The base change `mA` is a closed immersion, so `W_A` is affine; by the
affineness theorem `exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback`, `W_{T₀}` is affine for a
finitely generated `T₀ ⊇ s`. Over the affine schemes `V_{T₀}` and `W_{T₀}`, the base change of `m` is `Spec`
of a ring map `phi` of finite type (`phi`, `phi_finiteType`). For every `T₀`-algebra `S`, the global
sections of the base changes to `Spec S` are `S ⊗[T₀] Γ(-)` (`exists_ringEquiv_tmul`, from Mathlib's
`isPushout_appTop_of_isPullback`), so the morphism over `Spec S` is surjective on global sections iff
`S ⊗ phi` is surjective (`stage`, `surjective_iff_of_tmul`). Since `mA` is a closed immersion of affine
schemes, `A ⊗ phi` is surjective; the surjectivity theorem
`Algebra.TensorProduct.exists_fg_subalgebra_surjective_map_of_surjective_map` gives a finitely generated
`T₀`-subalgebra `T'` with `T' ⊗ phi` surjective, so the base change over `T'` is a closed immersion
(`IsClosedImmersion.of_surjective_of_isAffine`). Finally `T'` is rewritten as a finitely generated
`A₀`-subalgebra containing `s` (`Algebra.adjoin_union_eq_adjoin_adjoin`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.CIDescGC6.exists_ringEquiv_tmul`
- theorem `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.CIDescGC6.surjective_iff_of_tmul`
- abbrev `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.CIDescGC6.ι`
- scoped instance `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.CIDescGC6.algebraPullback`
- def `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.CIDescGC6.mBC`
- theorem `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.CIDescGC6.mBC_fst`
- theorem `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.CIDescGC6.mBC_snd`
- scoped unnamed instance `instance [LocallyOfFiniteType m] : LocallyOfFiniteType (mBC (R := R) m v)`
- def `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.CIDescGC6.phi`
- theorem `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.CIDescGC6.phi_apply`
- theorem `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.CIDescGC6.phi_finiteType`
- theorem `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.CIDescGC6.stage`
- theorem `P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback` (ported by the same task), `Langlands.AnthropicFLT.Theorems.Thm_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map` (ported by the same task).
All modules also import `Mathlib`.
