# Comparing regular families of twisted distributions

`RegularLinearFormComparisonStatement` concerns two families of complex
linear forms indexed by the complex torus `(ℂˣ)^n`. Each evaluation of
either family on a fixed test is represented by a Laurent polynomial.
For every point of the unitary torus, suppose the forms there are
proportional by a complex scalar whose `d`-th power is one. For `d > 0`,
one `d`-th root of unity relates the forms on the full complex torus.

The proof chooses Laurent polynomials for each test and applies
`exists_rootOfUnity_laurent_comparison`. This yields the same scalar for
all tests and parameters, hence equality of the corresponding linear forms.

`regularTwistedDistributionComparison` applies the proposition when the
unitary specializations are twisted distributions of equivalent admissible
irreducibles whose twisting operators have `d`-th power one. It uses
`exists_rootOfUnity_twistedDistribution_eq_smul_of_equiv` on each
specialization. The representations and their carriers can vary with the
point on the unitary torus.

This comparison can be applied to permutation of inducing blocks in the
distinct-exponent case of Henniart–Lemaire (2011), II.5.13, given regularity
for the two families with their chosen normalized operators and equivalence
of the underlying irreducible representations on the unitary torus.
Rogawski (1988), Lemma 11.1(a), gives fixed-test regularity for induced
families. The comparison uses Rogawski's convention `A^d = I` (p. 215).
Henniart–Lemaire II.5.2 allow `A^d = λ I` with `λ ≠ 0`. The scaling
in `FiniteOrder` converts a scalar-power operator to an identity-power
operator before forming the regular families.
