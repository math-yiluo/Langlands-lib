# Uniform approximation in a compact-finite translation-invariant space

Let `S` be a right-translation-invariant complex subspace of continuous
functions on a compact group, and suppose each vector in `S` has a
finite-dimensional right translate span. A continuous compact-finite
function uniformly approximable by `S` belongs to `S`.

A continuous reproducing weight fixes the given function under compact
convolution. Its left translate span is finite dimensional, so the
convolution outputs lie in a fixed finite-dimensional space of functions.
For each approximant, the convolution is in its right translate span
by integrating its finite-dimensional coordinates. These coordinates
are continuous because their linear forms are finite sums of point
evaluations. Thus all convolved approximants belong to the intersection
of `S` with the fixed finite-dimensional space. The uniform error is
multiplied by at most the integral of the norm of the weight. The
intersection is closed for pointwise convergence and contains the
function being approximated.

This internal lemma implements the compact projection step in the proof
of Proposition 7.1(vi) of H. Jacquet, *Archimedean Rankin–Selberg
Integrals* (2009), author pp. 46–47, through a reproducing weight on the
given translate span. [Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
