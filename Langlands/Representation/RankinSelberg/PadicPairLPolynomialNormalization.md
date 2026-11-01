# Constant-term normalization of p-adic pair L-polynomials

This module contains the existing normalization lemmas
`Langlands.RankinSelberg.IsPadicPairLPolynomial.coeff_zero` and
`Langlands.RankinSelberg.IsPadicSymmetricLPolynomial.coeff_zero`, relocated
from `LanglandsLFactor` without changing their statements or proofs. The
lemmas retain independent field and representation universes, the canonical
p-adic topology, the supplied additive character and Haar measure, and both
positive rank orders.

The ordered relation supplies an actual compatible quotient measure. Its
certificate at that measure gives `P.coeff 0 = 1` by the underlying
pair-polynomial normalization. The symmetric relation has the same
normalization in either rank-order branch. These are deductions from the
existing relations documented in [PadicPairFactors](PadicPairFactors.md)
and [PairLFactor](PairLFactor.md).

Keeping these lemmas beside the pair-factor definitions allows the adjacent
analytic gamma argument and the nongeneric Langlands-factor construction to
share them without importing classification interfaces into the analytic
argument. No factor-existence or functional-equation assertion is added.
