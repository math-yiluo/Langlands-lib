# Compact curves with prescribed skew-adjoint tangent

Author: Worker 84. Module:
`Langlands.Global.ArchimedeanCompactTangentStatement`.
The proposition is
`Langlands.Global.ArchimedeanGL.CompactTangentCurveStatement`.

For every `K : Type u` with `[Field K] [NumberField K]` and every `n : ℕ`,
the proposition states that each `X : compactLieSubalgebra K n` admits a
curve `c : ℝ → standardInfiniteCompact K n` satisfying `c 0 = 1` and

```lean
HasDerivAt
  (fun t : ℝ =>
    (archimedeanGLCoordinates K n (c t).val : ArchimedeanMatrix K n))
  (realLieAlgebraToMatrix K n (X : RealLieAlgebra K n)) 0
```

The curve takes values in the existing subgroup of the general linear group
over the actual archimedean completions. The subgroup enforces orthogonality
at real places and unitarity at complex places. The coordinate map is the
published `archimedeanGLCoordinates`; its value is coerced from invertible
matrices to the actual mixed real/complex matrix space. The derivative is
over `ℝ`, with the existing norm selected by `Matrix.Norms.Operator`.
The prescribed tangent uses the published real-linear identification
`realLieAlgebraToMatrix`. Compact Lie membership means skew symmetry at
real places and skew-Hermitian symmetry at complex places.

The curve is defined on all of `ℝ`, but only its matrix derivative at zero
is required. No continuity or smoothness away from zero is asserted.
There is no connectedness, positive-rank or additional finiteness
hypothesis. Rank zero is included. The final Lean example checks the entire
universe and parameter telescope:

```lean
(K : Type u) → [Field K] → [NumberField K] → ℕ → Prop
```

## Internal provenance and remaining proof obligation

This is an internally specified prerequisite for the compact curve/tangent
bridge needed by
[`CompactGroupFiniteDifferentialStatement`](ArchimedeanCompactGroupFiniteStatement.md).
It combines the existing compact subgroup, skew-adjoint Lie subalgebra and
matrix coordinates without changing those definitions. The motivating
proof obligations are described in that statement's companion and the
[automorphic differential-growth source map](../../notes/automorphic/differential-growth-source-map.md).
This module does not attribute the displayed proposition to an original
literature theorem.

The Lean file defines the target proposition; it does not prove it.
A later proof must construct curves in the actual subgroup and establish
the displayed derivative. Relating the curves to the published right-action
derivative in direction `gX`, preserving the finite compact-group orbit
under differentiation, and extending to the compact-generated enveloping
algebra remain separate obligations for the parent finiteness proof.
