# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation`

Ported module of the proof submitted by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` (descent of schemes of finite presentation along finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof. `MFPb6.HasModels A₀ h` says that `h : Y ⟶ Spec A` has models over finitely generated subalgebras
containing any given finite set (and the image of `A₀`). It is invariant under isomorphisms over
`Spec A` (`hasModels_of_iso`), holds for affine `Y` by the affine-case theorem with `R = A₀`
(`hasModels_of_isAffine`), and passes from two quasi-compact opens to their union by the gluing-step
theorem (`hasModels_of_sup`). Mathlib's `compact_open_induction_on` (every quasi-compact open is built
from `⊥` by adding affine opens) then gives models for every quasi-compact open of `X`; `X` itself is
quasi-compact because `g` is quasi-compact over the affine `Spec A`, and the open `⊤` is isomorphic to
`X` (`MFPb6.main`). The solution forgets the extra condition on the image of `A₀`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation.MFPb6.HasModels`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation.MFPb6.hasModels_of_iso`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation.MFPb6.hasModels_of_isAffine`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation.MFPb6.hasModels_of_sup`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation.MFPb6.isCompact_preimage_ι`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation.MFPb6.main`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation`.
All modules also import `Mathlib`.
