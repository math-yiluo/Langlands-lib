# Actual finite adelic action on horizontal cohomology

This internal construction specializes the generic horizontal quotient action
to an actual `OperatorRealization F n`. The number field `F : Type u` has
arbitrary universe, the natural rank `n` is positive, and coefficients are
complex in the existing `S.Space`. Every natural degree, including zero, is
retained.

The actual horizontal complex uses `compactInReducedSubmodule F n`,
`reducedCompactRepresentation F n` and `S.compactRepresentation`. Its bracket
covariance, coefficient covariance and all-degree insertion identity are the
same proved terms used in `HorizontalCohomology`. The additional action is
the existing `S.horizontalFiniteRepresentation`, and its commutation with
the actual differential is `S.horizontalDifferential_finite`. Neither an
action nor a commutation hypothesis is a new input.

`horizontalCyclesFiniteRepresentation q` is a
`Representation ℂ (FiniteAdelicGL F n) (S.horizontalCycles q)`.
`horizontalCohomologyFiniteRepresentation q` is a
`Representation ℂ (FiniteAdelicGL F n) (S.HorizontalCohomology q)`.
They specialize the generic restriction to cycles and quotient by the actual
boundaries inside cycles. Cycle and boundary invariance are therefore proved,
and the identity and multiplication laws are the laws of the constructed
representations.

`horizontalCyclesFiniteRepresentation_val` specializes the proved equality
between the underlying translated cycle and
`S.horizontalFiniteRepresentation q d f.val`.
`horizontalCohomologyFiniteRepresentation_class` specializes the proved
equality

```text
S.horizontalCohomologyFiniteRepresentation q d
  (S.horizontalCohomologyClass q f) =
S.horizontalCohomologyClass q
  (S.horizontalCyclesFiniteRepresentation q d f).
```

`horizontalCohomologyClassFiniteIntertwiner q` is the finite adelic
intertwiner from the cycle representation to the quotient representation.
Its `toLinearMap` is `S.horizontalCohomologyClass q`, as certified by
`horizontalCohomologyClassFiniteIntertwiner_toLinearMap`.
The formula abbreviations have inferred types from the actual generic proof
terms; they are proofs, with no additional assertion supplied by the caller.

The provenance is internal specialization of
`Langlands.Cohomology.Lie.Horizontal` using the already constructed actual
cochains, actual differential and actual finite action. Full equivariance for
every element of the standard infinite compact group, including its
disconnected components, is preserved. This module asserts no continuity or
smoothness of the entire quotient representation, finiteness, nonvanishing,
sheaf or analytic comparison, or injectivity into absolute cohomology.

Authorship: Worker 2.
