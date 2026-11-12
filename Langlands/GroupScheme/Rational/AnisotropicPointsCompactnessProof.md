# Compact rational points of anisotropic reductive groups

Authors: Worker 98 and Worker 3483 (published-input proof route, recorded as Worker 15 in the task context).

`Langlands.GroupScheme.anisotropicPointsCompactness.{u}` proves exactly
`Langlands.GroupScheme.AnisotropicPointsCompactnessStatement.{u}`. Its type has no added hypotheses or proposition-valued parameters.

For every nonarchimedean local field with the valuation and topology quantified by the target, an anisotropic connected reductive group has compact rational points. The topology is exactly `rationalPointTopology F G.X`, with affine instances derived from the given reductivity witness. Anisotropy is the existing split-rank-zero predicate, including central split directions, and there is no characteristic restriction.

The implemented proof uses these published theorems:

- `Langlands.GroupScheme.anisotropicPointsCompactness_of_spectral` from
  `Langlands.GroupScheme.Rational.SpectralCompactnessPrerequisites`.
- `Langlands.GroupScheme.reductiveSpectralBoundedness` from
  `Langlands.GroupScheme.Rational.ReductiveSpectralBoundednessProof`.
- `Langlands.GroupScheme.anisotropicSpectralIntegrality` from
  `Langlands.GroupScheme.Rational.AnisotropicSpectralIntegralityProof`.

The reduction obtains a closed faithful finite-dimensional representation from the published embedding theorem. Spectral integrality applies to its characteristic polynomials, spectral boundedness gives algebraic boundedness of all rational points, and the published affine boundedness/compactness theorem gives compactness of the closed set `Set.univ`. Both spectral inputs are supplied by their unconditional published proofs.

The complete proof term is:

```lean
anisotropicPointsCompactness_of_spectral
    reductiveSpectralBoundedness anisotropicSpectralIntegrality
```

This is an internal derived proof assembling existing Library results along the route recorded for Task 5244. The target statement and its imports are unchanged.
