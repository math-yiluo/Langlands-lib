# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation`

Ported module of the proof submitted by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` (descent of schemes of finite presentation along finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 3 `p2m_reactivate` command(s) (an FLT command from `P2M.Util` that re-activates scoped extensions) are removed; the file compiles without them.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof. Descend `e.hom` and `e.inv` separately with the morphism-descent theorem, to stages `T₁` and `T₂`,
and base change both to `B = T₁ ⊔ T₂` (`IsoDesc.bc`, compatibilities `bc_compat`, `stMap_stMap`). The two
composites `gB ≫ hB` and `hB ≫ gB` become the identity after base change to `A`; the equality-descent
theorem (applied over `B`, `IsoDesc.exists_fg_stMap_comp_eq`) gives finitely generated `B`-subalgebras
`T'`, `T''` over which they are the identity. With `T = (T' ⊔ T'').restrictScalars A₀` (finitely
generated and containing `B` by `Subalgebra.fg_restrictScalars_and_le_of_fg`), the base changes of
`gB` and `hB` to `T` are inverse isomorphisms, and the compatibility with `e` follows from `bc_compat`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.XR`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.spec_comp`
- def `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.stMap`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.stMap_fst`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.stMap_snd`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.eq_stMap`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.stMap_stMap`
- def `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.bc`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.bc_fst`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.bc_snd`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.bc_stMap`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.bc_compat`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.inclusion_comp_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.val_comp_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.val_comp_inclusion`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.IsoDesc.exists_fg_stMap_comp_eq`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType`, `Langlands.AnthropicFLT.Theorems.Thm_Subalgebra_fg_restrictScalars_and_le_of_fg`.
All modules also import `Mathlib`.
