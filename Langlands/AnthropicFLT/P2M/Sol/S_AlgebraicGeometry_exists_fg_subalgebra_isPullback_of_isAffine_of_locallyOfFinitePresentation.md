# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation`

Ported module of the proof submitted by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` (descent of schemes of finite presentation along finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

Proof of the affine case (`m1_main`). The index type `Idx s` consists of the finitely generated
`A₀`-subalgebras of `A` containing `s` and the image of `R`; it is directed, the inclusions form a
directed system, and `A` is its direct limit (`M1b3.isDirectLimit`). The index type is nonempty because
`R` is of finite type over `A₀`. With `B = Γ(X, ⊤)`, the ring map `A → B` is of finite presentation and
`g` is `Spec` of it up to `X.isoSpec`. The tensor-product theorem of
`Thm_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit` gives a stage `T` and a
finitely presented `T`-algebra `A'` with `A ⊗[T] A' ≅ B`. Take `X₀ = Spec A'` with the structure map
`f₀`. The pullback square is `Spec` of the pushout square of the tensor product
(`isPullback_SpecMap_of_isPushout`, `CommRingCat.isPushout_tensorProduct`), transported along the
isomorphism `X ≅ Spec (A ⊗[T] A')`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation.M1b3.Idx`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation.M1b3.idx_directed`
- scoped unnamed instance `instance (s : Finset A) : IsDirected (Idx (A₀ := A₀) (R := R) s) (· ≤ ·)`
- scoped unnamed instance `instance (s : Finset A) : IsDirectedOrder (Idx (A₀ := A₀) (R := R) s)`
- def `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation.M1b3.stageMap`
- instance `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation.M1b3.directedSystem`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation.M1b3.isDirectLimit`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation.m1_main`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`, `Langlands.AnthropicFLT.Theorems.Thm_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit`.
All modules also import `Mathlib`.
