# Equivariant Lie retraction onto the reduced archimedean algebra

This internal construction extends the actual normalized real-trace projection
from `ArchimedeanSplitCenter` to real and complex Lie homomorphisms. It works
over any field `K` in an arbitrary universe. Projection constructions require
`[NeZero n]`, because the real trace is divided by the rank.

The real projection subtracts the real scalar matrix whose scalar at each
infinite place is the real part of the trace divided by `n`. It retracts the
actual reduced Lie subalgebra, preserves the commutator, and commutes with every
actual infinite adelic conjugation. Thus the reduced condition is zero trace
at real places and zero real part of the trace at complex places; imaginary
scalar directions at complex places are retained.

Writing `s` for `splitCenterScalar` and `c` for `splitCenterCoordinate`, the
underlying real map is the existing

```text
p(X) = X − s(c(X)),       c(X) = n⁻¹ • realTrace(X).
```

`reducedLieProjection` equips this map with the proved Lie-homomorphism law.
`reducedProjection_reduced` is its retraction identity on the actual reduced
subalgebra. `realLieConjugation_splitCenterScalar` holds without a rank
restriction; `reducedProjection_conjugation` requires positive rank and
holds for every `g : InfiniteAdelicGL K n`.

`reducedComplexProjection` extends this real Lie homomorphism over `ℝ → ℂ`.
Its pure tensor formula is

```text
pℂ(z ⊗ X) = z ⊗ p(X).
```

It satisfies the following exact identities, with `j` the existing
`reducedComplexInclusion`:

```text
pℂ(j(X)) = X,
pℂ(compactComplexInclusion(Y)) = compactToReducedComplex(Y),
pℂ(Ad(g)(X)) = Ad_reduced(g)(pℂ(X)).
```

The first identity proves surjectivity. Both `pℂ` and `j` are complex Lie
homomorphisms, so their bracket preservation is part of their bundled types.

The real bracket proof uses that split scalar matrices are central and that
the real trace vanishes on a commutator. Conjugation fixes those scalar
matrices and preserves the real trace, proving projection equivariance.
Tensor induction proves the complex retraction and conjugation formulas.
These are consequences of the existing matrix constructions; no comparison
with an external literature object or supplied compatibility is assumed.

No number-field, finite-dimensionality or coefficient hypothesis is added.
These are algebraic maps; no new topology or analytic identification is
asserted. Reduced cochain maps, the relative differential and cohomology are
separate constructions.
