# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation`

Ported for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (existence of quotients of projectively embedded abelian schemes by finite étale subgroups) by Worker 1224. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT file ends with the diagnostic command `#print axioms solution`, which only prints the axioms used and adds nothing to the environment; the port drops it.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `solution` proves the statement of
`AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation` (companion module
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation`):
if `f : X ⟶ Y` is smooth, surjective and quasi-compact, `f ≫ g` is smooth and `g` is locally of finite
presentation, then `g` is smooth.

Proof. It suffices that the smooth locus of `g` is everything (`Scheme.Hom.smoothLocus_eq_top_iff`). A point
of `Y` is `f x`. Choose affine opens `U ∋ g (f x)` of `Z`, `V ∋ f x` of `Y` inside `g⁻¹ U` and `W ∋ x` of `X`
inside `f⁻¹ V`. Then `Γ(Z, U) → Γ(Y, V)` is of finite presentation and `Γ(Y, V) → Γ(X, W)` is smooth; smoothness
of `f ≫ g` at `x` gives `Algebra.IsSmoothAt Γ(Z, U)` at the prime of `x` (`formallySmooth_stalkMap_iff`). The prime
of `f x` is the contraction of the prime of `x` (`IsAffineOpen.comap_primeIdealOf_appLE`), so the ported
`Algebra.IsSmoothAt.of_isSmoothAt_of_smooth` gives smoothness of `Γ(Y, V)` over `Γ(Z, U)` at the prime of `f x`,
which is smoothness of `g` at `f x` by `formallySmooth_stalkMap_iff` again.

The hypothesis `QuasiCompact f` is part of the FLT statement but is not used in this proof: no step
consumes it, and the same proof text also compiles when `[QuasiCompact f]` is removed. The ported
statement keeps the hypothesis unchanged.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth` (already in the Library, with its own imported FLT ports).
Other imports: `Mathlib`.
