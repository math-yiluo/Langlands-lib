# Finite scalar comparisons for regular families

Suppose two families in an integral domain agree up to a scalar at every point
of a separating family of evaluations. The scalar can depend on the evaluation
but belongs to a fixed finite set. If no scalar works in the coefficient domain,
choose a test witnessing failure for each scalar. The product of the differences
is nonzero in the domain. At each evaluation one of its factors is zero, so the
product vanishes at every evaluation. This contradicts separation.

For Laurent polynomials over `ℂ`, evaluation on the unitary torus is separating
by `finiteLaurent_eq_zero_of_eval_unitary`. If the comparison scalars have
`d`-th power one, they belong to the finite set `Polynomial.nthRootsFinset d 1`.
The resulting common scalar compares the whole family on the complex torus,
including at parameters outside the unitary locus.

This derived algebra lemma applies to twisted characters of induced families
when pointwise comparisons of finite-order intertwiners are available.
