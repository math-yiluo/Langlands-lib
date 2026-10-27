# Compact differentiation on actual reduced horizontal cochains

This internal construction derives infinitesimal compact equivariance for
alternating cochains on the actual reduced archimedean Lie algebra. It extends
them along the normalized real-trace projection, applies the proved ambient
compact differentiation theorem, and restricts back to the reduced algebra.

Write `g` for `ComplexLieAlgebra K n`, `g₀` for
`ReducedComplexLieAlgebra K n`, `j : g₀ → g` for
`reducedComplexInclusion`, and `p : g → g₀` for
`reducedComplexProjection`. These are the existing actual complex Lie maps,
with `p(j(X)) = X`. Here `g₀` is the scalar extension of the coordinatewise
real-trace kernel; at complex places this retains imaginary scalar directions.

For any field `K : Type u`, rank `n` with `[NeZero n]`, degree `q : ℕ`, and
complex module `V : Type v` in an independent universe, the complex-linear map
`reducedCochainExtension K n q` is

```text
E(f)(X₁, …, Xq) = f(p(X₁), …, p(Xq)).
```

It is constructed by alternating-map precomposition, so requires no topology
or finite-dimensionality of `V`. Its restriction to the tuple
`(j(X₁), …, j(Xq))` equals `f(X₁, …, Xq)`, which also proves injectivity.
For any representation `ρ` of the full group `standardInfiniteCompact K n`
on `V`, full compact equivariance of `f` implies full compact equivariance of
`E(f)`. The proof uses the actual conjugation-equivariance of `p`. No
equivariance hypothesis is restricted to the identity component.

For the differentiation construction, let `F : Type u` be a number field and
`S : OperatorRealization F n`. The coefficients are exactly `S.Space`.
`reducedCochain_compact_complex` proves, for every full compact equivariant
reduced cochain `f`, every `Y : CompactComplexLieAlgebra F n`, and every
tuple `X : Fin q → ReducedComplexLieAlgebra F n`, that

```text
S.compactLieAction Y (f X)
  = ∑ i : Fin q, f (Function.update X i [ι(Y), X i]),
```

where `ι = compactToReducedComplex F n` and the bracket is the actual
matrix commutator after scalar extension. There are no signs in this
insertion identity, since the replaced input stays in its original position.

The proof first applies `S.cochain_compact_complex` to `E(f)` and the
included tuple `j ∘ X`. The retraction identity identifies its left side.
For every term of the right side, the Lie-homomorphism property of `p` and
the proved identities

```text
p(compactComplexInclusion Y) = ι(Y),    p(j(X i)) = X i
```

identify the projected bracket with `[ι(Y), X i]`. Function extensionality
and a case split on the updated coordinate give the displayed sum.
Thus infinitesimal compatibility is derived from the ambient differentiation
theorem and actual projection maps.

`reducedInfinitesimalCompactCochains` is the submodule of all reduced
alternating cochains satisfying precisely this insertion identity for every
`Y` and `X`. Closure follows from the complex linearity of the coefficient
Lie action, pointwise cochain operations, and finite sums.
`mem_reducedInfinitesimalCompactCochains` states its exact defining
predicate. This submodule itself is defined for every rank; the proof
using the normalized projection requires `[NeZero n]`.

`reducedCompactEquivariantLieInclusion` sends a full compact equivariant
reduced cochain to the identical cochain in this infinitesimal submodule.
It is complex-linear and injective, with target membership supplied by the
proved differentiation theorem.

`infinitesimalHorizontalCochains` is the intersection of that infinitesimal
submodule with the existing horizontal submodule: a cochain vanishes
whenever any input belongs to the actual image of the compact complex Lie
algebra in `g₀`. `horizontalCompactLieInclusion` sends the existing
`horizontalEquivariantSubmodule` into this intersection, preserving the
underlying cochain and its horizontal condition. It too is complex-linear
and injective. Its construction derives the infinitesimal condition and
retains the already proved horizontal membership.

The degree `q` is unrestricted. In degree zero the insertion sum is empty
and horizontality is vacuous, so the unique cochain value is killed by every
compact complex Lie direction. The construction only proves the implication
from full group equivariance to the infinitesimal identity. No converse is
claimed for the potentially disconnected full compact group.

General algebraic coefficient attachment, a differential on horizontal cochains,
square zero and relative cohomology are separate obligations.

The provenance is internal: the extension and restriction identities follow
from `ArchimedeanReducedProjection`, equivariance uses the existing actual
adjoint representations, and the differentiated identity follows from
`CochainCompactDifferentiation`. This module asserts no additional
identification with an external cohomology theory.
