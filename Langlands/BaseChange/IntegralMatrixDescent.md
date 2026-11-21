# Integral descent for matrix cocycles

This module develops an algebraic ingredient for the unit fundamental lemma.
A spanning set of column vectors over a local ring still spans after
reduction. Choose independent reduced columns from that image and lift them
from the original generating set. Their reduced determinant is nonzero, so
the lifted columns form a matrix with unit determinant.

The semilinear vector operator applies the scalar automorphism coordinatewise
and then multiplies by the given matrix. Its `l`-fold iterate acts by the
Library's ordered cyclic norm after applying the `l`-th power of the scalar
automorphism. The trivialization theorem assumes `0 < l`, `σ ^ l = 1`, and
`cyclicNorm σ l g = 1`. It also assumes that some scalar `a` satisfies
`IsUnit (σ^i(a) - σ^j(a))` for all distinct `i, j` in `Fin l`. The cyclic
fixed-span lemma applies under these hypotheses. The fixed columns of a unit
matrix `c` then satisfy `g * σ(c) = c`, the required trivialization of the
integral matrix cocycle.
