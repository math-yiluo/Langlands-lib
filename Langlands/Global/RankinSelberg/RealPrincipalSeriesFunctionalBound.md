# A derivative estimate for extending real Whittaker evaluations

The submodule `twistedDifferences` of the smooth expanded position
principal series is spanned by `R(u)x − ψₐ(u) x` for upper-unipotent
`u` and smooth source vectors `x`. A complex-linear form obeys the
Whittaker law exactly when it vanishes on this submodule.

`HasTwistedEvaluationBound` asks for a finite list of right derivative
words and a nonnegative constant. The norm of the identity evaluation
of a given K-finite coefficient map at `f` must be bounded by this
constant times the sum of the compact supremum norms of those
derivatives of `f + z`. Here `f` is included into the smooth expanded
source and `z` ranges over the twisted differences.

This bound is equivalent to the existence of a compact-derivative-bounded
Whittaker form on the expanded smooth source with the given evaluations.
In the forward direction the evaluation on pairs `(f, z)` descends to
the range of the finite compact coordinate map of `f + z`. The estimate,
with the constant multiplied by the number of coordinates, bounds
the resulting linear form in the product supremum norm. Hahn–Banach
extends it to the whole product. Composing with the compact coordinate
map of the smooth source gives the required form. Taking `f = 0`
shows it vanishes on twisted differences, and taking `z = 0` verifies
its values on source vectors. The reverse implication follows by
applying the form's bound to each `f + z`.

`RealUniformPrincipalSeriesTwistedBoundReductionStatement` applies the
criterion and the evaluation reduction to the original extension
problem. Its premise `RealUniformPrincipalSeriesTwistedBoundStatement`
asks for the derivative estimate for each given uniform map of an
inducing list of the stated rank with a nonzero induced weight.
This is a Library-specific formulation of the scalar extension step
related to smooth Whittaker exactness.
[Jacquet, *Archimedean Rankin–Selberg Integrals*, Lemma 2.4 and §11](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
[Casselman, Hecht, and Miličić, *Bruhat filtrations and Whittaker vectors for real groups*, §8](https://www.math.utah.edu/~milicic/Eprints/whittaker.pdf)
