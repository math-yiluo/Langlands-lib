# Actual finite numerators at the equal-rank boundary

This internal deduction combines `EqualTwoSidedFirstBlockLaws` with the
published lower support theorem and bilateral Laurent numerator extraction.
It does not assert either final dominant-rank gamma or L proposition.

`EqualFirstBlockFactorCertificate` retains the complete first-block epsilon
equation, the central minus-one scalar, and both normalized polynomial
generators for every complementary pair of rectangle sizes.

`EqualTwoBlockFiniteNumerators` chooses both certificates before all sections,
test-model coefficients, and row Fourier pairs. The reversed first-block
certificate has original polynomial `P₂D` and dual polynomial `P₂`.
Its dual coefficient is that of the functional transported through the same
fixed reversed-dual section equivalence as the lower Fourier law, evaluated
at the first-dual test-model coefficient and the supplied Fourier transform.

`equalTwoBlockFiniteNumerators_of_laws` extracts the two complete certificates
from the supplied actual two-sided laws. Full type of the original lower
induction follows from full type of its blocks. Full type of both reversed
blocks and the test's inverse transpose follows from the published duality
theorems, and the same induction theorem gives full type of the reversed lower
induction. Thus `equalRankSliceSupport` gives both lower support bounds for
the actual coefficient series, with no extra support or induced-type premise.
The lower Fourier law supplies the reflected coefficient identity, and
`twoBlock_cleared_numerators` extracts a unique finite Laurent numerator.

The original numerator is cleared by `(P₁ * P₂).toLaurent`. Its reflected
numerator is cleared by the product of the dual polynomials, multiplied by
the reflection of the inverse of the specified Laurent unit. The effective
block constants are `ζ₁ ^ t * c₁` and `ζ₂ ^ t * c₂`; no clearing factor is
cancelled on bilateral coefficient series.

`exists_equalTwoBlockFiniteNumerators` discharges the two-sided-law premise
above the real opposite-twist bound of `exists_equalTwoSidedFirstBlockLaws`.
It retains absolute convergence of every ordinary Jacquet section and a
nonzero ordinary realizing functional `Ju`, chosen before the three quotient
measures. For each compatible triple, the complete block certificates precede
all sections, model coefficients and Fourier pairs. Those certificates may
depend on the triple of quotient measures.

The field, test carrier, and dependent block carriers retain independent
universes. All quotient measures are supplied and compatible with the canonical
Haar measures. The existence theorem requires right invariance of the
unipotent Haar measures at the total rank and both block ranks, full Whittaker
type of the test and both base blocks, and nonzero test and base block
functionals. It requires neither irreducibility nor an analytic first-block
or Fourier identity as an additional premise.

This construction concerns sufficiently large real opposite twists at equal
rank. Ordinary Jacquet convergence does not assert lower-slice or outer
spectral convergence. Convergence of scalar spectral expansions, rational
continuation, the undeformed parameter, the strict dominant case, and final
factor identities remain separate obligations.
