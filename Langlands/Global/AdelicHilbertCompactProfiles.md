# Compact profiles of adelic Hilbert vectors

For a Hilbert action `π`, an archimedean compact subgroup `K` and a continuous
linear form `ℓ`, the profile of `v` is the function `k ↦ ℓ(π(k)v)` on `K`.
`hilbertCompactProfileSubspace` consists of the vectors for which each of these
profiles belongs to a prescribed subspace `E`. For finite-dimensional `E` this
is a closed subspace. Each profile map is continuous for pointwise convergence
on functions on `K`, and the defining condition is an intersection of preimages
of the closed finite-dimensional subspace.

If the compact orbit of `w` spans a finite-dimensional space `W`, take `E` to
be the image of the algebraic dual of `W` under evaluation on that orbit.
Continuity of the orbit and of linear forms on `W` gives continuous profiles.
Left translation of a profile corresponds to precomposing its linear form with
an operator preserving `W`, so `E` is stable under left translation. In
particular all profiles of `w` belong to `E`.

`exists_hilbertCompactProfileProjection` applies the scalar reproducing weight
of `exists_reproducing_adelicCompactProfileWeights` to the matrix coefficients
`x ↦ ℓ(π(x)v)`. Moving `ℓ` through the Bochner integral gives a weighted compact
average that sends every vector into the profile subspace. On that subspace
all scalar coefficients are reproduced at the identity. Testing with the
inner product against the difference of the average and the original vector
proves that the average fixes the subspace. This derives the Hilbert-space
projection directly from the scalar compact averaging identities.
[Adelic compact profile projection](AdelicCompactProfileProjection.md)
