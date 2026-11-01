# Actual zeta operators for regular matrix tests

This is a derived helper for the supercuspidal matrix functional equation.
It constructs an operator from the published integrated Hecke action, on the
original algebraic complex representation carrier. The field and carrier
universes are independent, and no topology or completeness is imposed on the
carrier.

A full-matrix Schwartz test which vanishes on every singular matrix restricts
to an actual compactly supported, locally constant function on GL. The
published `regularMatrixTestRestriction` proves this compactness. The actual
residue-normalized determinant weight at any complex exponent is locally
constant: it factors through the continuous integer-valued determinant order.
Multiplying the restricted test by this weight therefore gives the group test
`weightedRegularMatrixTest`.

`regularMatrixZetaOperator` integrates this group test against the given smooth
representation using `Hecke.integratedAction`. The latter is the actual finite
sum integral of the compactly supported, locally constant orbit integrand; its
definition does not require a vector-valued Bochner integral. The operator is
complex linear in the matrix test and in the representation vector.

Every algebraic linear functional evaluates this operator as the actual scalar
matrix integral, with the canonical p-adic topology, normalized determinant
absolute value and shared normalized group Haar measure. The integrand is
locally constant and compactly supported, so it is absolutely integrable at
every complex exponent. Admissibility makes the operator finite rank by the
published finite-rank theorem for the integrated Hecke action.

This module provides the operator construction and scalar evaluation identity.
It does not claim that a Fourier-regular test realizes a nonzero operator,
that arbitrary finite-rank operators are realized, or that any functional
equation or scalar gamma factor exists.

The canonical field, topology and group measurable instances have explicit
module-specific declaration names. This keeps their generated names from
colliding with other modules in `Langlands.GodementJacquet.Padic`; the
instance values, hypotheses and proofs are unchanged.
