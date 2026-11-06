# Probability Haar averaging of a continuous isometric action

`compactProbabilityHaar K` is actual Haar measure on a compact topological
group `K`, normalized using the positive compact whole group. Its mass on
`Set.univ` is one. It is a regular Haar measure on the supplied Borel space;
it is not the restriction of an ambient group's Haar measure.

For a second countable such group and a complete normed complex vector
space `E`, supply an original monoid homomorphism
`π : K →* (E →L[ℂ] E)`, preservation of vector norms and continuity of every
orbit. `compactIsometricAverage K π hnorm hcont` is the continuous complex
linear operator whose value on `x` is exactly

```
∫ k, π k x ∂compactProbabilityHaar K.
```

Continuous orbits are strongly measurable because the source is second
countable. Norm preservation and the integrable constant weight one give
absolute Bochner integrability. The operator is constructed by the existing
`integratedIsometricAction`, and the probability normalization gives its
operator norm at most one. No smoothness or open stabilizer is required of
an input vector.

Left invariance of the actual Haar measure makes every output fixed by
`π`. Conversely, the integral of a fixed vector is that vector, by mass
one. The operator therefore retracts exactly the original fixed-vector
set and is idempotent as a bounded operator. A supplied continuous complex
linear intertwiner commutes with these averages: pass the intertwiner
through the absolutely convergent Bochner integral and use its pointwise
intertwining identity. This also applies to inclusions and non-isometric
projections.

Provenance is internal. The construction specializes the published bounded
isometric-orbit integral to weight one and uses pinned Mathlib's
`Measure.haarMeasure`, normalization on a positive compact, Bochner
integral commutation with continuous linear maps and invariance under left
multiplication. The fixed-vector and retraction identities verify this
constructor directly. This analytic average complements the existing
finite-orbit averaging for already smooth representations; it does not
claim equality with that algebraic constructor, a density theorem,
archimedean smoothness, admissibility, or a spectral decomposition.
