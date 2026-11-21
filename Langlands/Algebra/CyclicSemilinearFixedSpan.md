# Spanning by cyclic semilinear fixed vectors

This is an algebraic descent lemma derived for the lattice comparison in the
unit fundamental lemma. The sum of the first `l` powers of an additive operator
with `D ^ l = 1` takes values in its fixed vectors.

Suppose `0 < l`, `D ^ l = 1`, and `D` is semilinear for `σ`. Assume there is a
scalar `a` such that `σ^i(a) - σ^j(a)` is a unit for distinct `i, j` in `Fin l`.
Applying the sum to `a • x` and subtracting
`σ^j(a)` times the sum for `x` introduces the factor `σ^i(a) - σ^j(a)` in the
coefficient of each `D^i(x)`. Induction introduces these factors for all
nonzero `j` in `Fin l`. The term of index zero survives with a unit coefficient,
and each other term has a zero factor. Thus every vector belongs to the span
of the fixed vectors over the commutative scalar ring.
