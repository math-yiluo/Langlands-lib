# Finite compact types in the actual generated differential module

Author: Worker 94.

`Langlands.Global.ArchimedeanGL.generatedCompactTypeFiniteness` proves the
published `GeneratedCompactTypeFinitenessStatement K n` for every number
field in arbitrary universe and every natural rank, including zero. The
actual compact and center finiteness hypotheses are retained, and the
statement and its imports are unchanged.

For the given compact-finite, center-finite actual smooth vector `f`, the
common-annihilator theorem supplies one center ideal `I` with a
finite-dimensional complex quotient. This ideal annihilates every vector
in the actual generated span of `compactAction k (operator a f)`.

The proved `compactTypeCentralSpan` supplies finitely many vectors `v i`
in that span whose full center orbits cover its intersection with any
selected actual compact type. Each vector is killed by the same ideal
`I`. Transport through `toSmooth` gives the corresponding smooth center
action equation. The quotient-orbit theorem then proves that each such
center orbit is a finite-dimensional image of the center quotient.

Linear images, finite sums and subspaces preserve finite dimension.
Applying these three facts to the covering proves exactly the required
finite-dimensional compact-type intersection. The argument also covers
an empty family of covering vectors.

This proof is derived from the actual common-annihilator construction,
the finite central covering, and the center-quotient orbit map. It
assumes no additional central spanning, analyticity or reproduction
statement. It concerns the algebraic generated module; extending to a
closed full group orbit and proving automorphic differential growth
remain separate obligations.
