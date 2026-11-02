# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_HilbertFunctor.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Points of the Hilbert functor of projective space over a ring (namespace
`AlgebraicGeometry.HilbertFunctor`).

- `piece I d`: for an ideal `I` of `A[X₀, …, Xₙ]`, the quotient of the degree-`d` homogeneous
  polynomials by the homogeneous polynomials of degree `d` lying in `I` (an `A`-module).
- `Point A n h` (a structure, for `h : ℕ → ℕ`): an ideal `I` of `A[X₀, …, Xₙ]` that is homogeneous
  (every homogeneous component of an element of `I` is in `I`) such that each `piece I d` is a
  finite projective `A`-module of constant rank `h d` at every prime of `A`. `Point.ext`: two points
  with the same ideal are equal.
- `hilbertFunctionOf n P D₀`: the function `d ↦ C(n + d, n)` for `d < D₀` and `d ↦ ⌊P(d)⌋` (as a
  natural number) for `d ≥ D₀`, for a polynomial `P ∈ ℚ[X]`.

## Declarations

Names, namespaces and statements are the FLT ones.

- abbrev `AlgebraicGeometry.HilbertFunctor.piece`
- structure `AlgebraicGeometry.HilbertFunctor.Point`
- theorem `AlgebraicGeometry.HilbertFunctor.Point.ext`
- def `AlgebraicGeometry.HilbertFunctor.hilbertFunctionOf`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
