# Compact tangent curves from matrix exponentials

Author: Worker 459. Module:
`Langlands.Global.ArchimedeanCompactTangentProof`.

The theorem
`Langlands.Global.ArchimedeanGL.compactTangentCurve` proves the published
`Langlands.Global.ArchimedeanGL.CompactTangentCurveStatement K n` for every
`K : Type u` with `[Field K] [NumberField K]` and every `n : ℕ`, including zero.
The target is imported from
[`ArchimedeanCompactTangentStatement`](ArchimedeanCompactTangentStatement.md).
Its definitions and conventions are unchanged.

## Implemented proof

For `X : compactLieSubalgebra K n`, set
`A = realLieAlgebraToMatrix K n (X : RealLieAlgebra K n)`.
Compact Lie membership gives `star A = -A`. The scalar `t` is real, so
`t • A` is also skew-adjoint.

Work in the actual mixed matrix algebra `ArchimedeanMatrix K n`, with the
operator norm selected by `Matrix.Norms.Operator`. Mathlib's
`NormedSpace.exp_mem_unitary_of_mem_skewAdjoint` proves
`exp (t • A) ∈ unitary (ArchimedeanMatrix K n)`.
`Unitary.toUnits` supplies the corresponding invertible matrix `g t`.

The two private star monoid homomorphisms `realMatrixProjection` and
`complexMatrixProjection` take a mixed matrix to its matrix at one real or
complex infinite place. They are entrywise ring projections and preserve
matrix star, which is transpose with coefficient conjugation.
`Unitary.map_mem` therefore shows that each real projection of `g t` is
orthogonal and each complex projection is unitary. The private lemma
`coordinates_unitary_mem_compact` applies the published
`mem_standardInfiniteCompact_iff` to conclude that
`(archimedeanGLCoordinates K n).symm (g t)` belongs to the actual
completion-based subgroup `standardInfiniteCompact K n`.
The curve `c` is this element together with its membership proof.

At zero, `exp (0 • A) = 1`; subtype extensionality, the injective coordinate
equivalence and extensionality of invertible matrices give `c 0 = 1`.
Mathlib's Banach algebra theorem `hasDerivAt_exp_smul_const A 0` simplifies to

```lean
HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0
```

The published coordinate equivalence cancels its inverse, and the underlying
matrix of `Unitary.toUnits` is the original exponential. Thus this is exactly
the required derivative of the mixed coordinates of `c`. No interchange of
coordinatewise infinite sums is needed.

## Provenance and scope

This is an internal derived proof of the existing target, using Mathlib's
matrix algebra, unitary group and Banach algebra exponential results. It
does not claim to reproduce a theorem or proof from the original literature.
The relevant imported Mathlib modules are
`Mathlib.Analysis.Normed.Algebra.Exponential` and
`Mathlib.Analysis.SpecialFunctions.Exponential`.

The construction assumes no connectedness, positive rank, finite compact-group
orbit or additional regularity. The curve is defined for all real parameters,
and the theorem establishes its derivative at zero. No nonempty matrix-index
assumption is used. The final Lean example checks the complete universe and
parameter telescope. This result supplies compact tangent curves; the
compact-group-finiteness and automorphic-growth implications are separate
proof obligations.
