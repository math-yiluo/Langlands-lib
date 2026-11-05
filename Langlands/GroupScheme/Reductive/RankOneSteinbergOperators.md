# Rank-one divided-power operators at Steinberg exponents

This internal construction considers the explicit integral divided-power
raising and lowering matrices `SplitExistence.gamE m a` and `gamF m a`, which
are defined for every natural weight `m`. The definitions `raising` and
`lowering` map those matrices into a field. The type
`DividedPowerInvariantSubmodule` consists of actual vector subspaces stable
under every one of these specified matrices.

The first arithmetic lemma proves that in characteristic `p`, every binomial
coefficient in row `p^s-1` equals the corresponding power of `-1`. Pascal's
recurrence and divisibility of the interior binomial coefficients in row
`p^s` give an induction. Thus every such coefficient is nonzero in a field.

The simplicity criterion is proved directly from the matrices. Choose the
least nonzero coordinate of a nonzero vector in a stable subspace. A divided
raising power sends that vector to a nonzero multiple of the top basis
vector: lower coordinates were zero and higher coordinates are shifted
past the end. Division gives the top basis vector, and divided lowering
powers give every other basis vector with coefficient one. Hence any such
subspace is zero or the entire space. The nonzero binomial coefficients
apply this argument at every Steinberg exponent `p^s-1`.

This is a concrete rank-one operator calculation, derived from the published
matrix formulas. It does not assert an actual algebraic-group representation
for arbitrary `m`, identify the operators with a group's distribution action,
or prove irreducibility of the induced covariant coordinate space. Those
comparisons and the higher-rank highest-weight theory remain obligations.
In particular the separate function `SplitExistence.gam m` is only the intended
small representation for `m ≤ 3`; no argument here treats it as a general
highest-weight representation.
