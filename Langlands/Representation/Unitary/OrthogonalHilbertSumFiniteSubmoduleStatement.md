# Finite-dimensional submodules of an orthogonal Hilbert sum

Let `E` be a complex Hilbert space with an internal Hilbert sum of complete
submodules `V i`. The summand maps in `IsHilbertSum` are their inclusions into
`E`. Let `W` be a finite-dimensional complex submodule preserved by every
orthogonal projection onto `V i`.

`Langlands.Analysis.OrthogonalHilbertSumFiniteSubmoduleStatement` says that
the indices for which `W ⊓ V i` is nonzero form a finite set of size at most
`dimℂ W`. For each vector of `W`, its projections onto this same set of
summands add up to the vector. The equality with the supremum of the
intersections is an algebraic submodule equality. The intersections are
mutually orthogonal by the Hilbert sum hypothesis.

The proposition extracts the finite-dimensional step used in the number-field
case of Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Theorem 9.7.3, printed pp. 266–267 (PDF pp. 278–279), after (9.43).
There the fixed space is prescribed by a finite set of archimedean compact
types, a compact open finite level and a finite-codimension ideal of the
enveloping centre. Given preservation by the summand projections, a choice of
one nonzero vector from each nonzero intersection gives an orthogonal,
linearly independent family in the fixed space. The Hilbert projection formula
therefore uses a finite set of indices, with the cardinal bound supplied by
linear independence. The automorphic application also requires the finiteness
and projection preservation of the fixed space.

Source `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
