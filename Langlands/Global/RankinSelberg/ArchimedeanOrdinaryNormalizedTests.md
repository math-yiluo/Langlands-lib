# Normalization and generation for ordinary archimedean integrals

`ArchimedeanOrdinaryNormalizedTestsStatement` gives the local inputs for
normalizing the ordinary partial Rankin–Selberg integrals. Its four
clauses concern continuation and generation at real and complex places.
The integrals use the Library's `realWhittakerModel` and
`complexWhittakerModel`, with additive parameters `a` and `-a`, and the
actual compatible measures on the unipotent quotients. In equal rank a
test includes an arbitrary Schwartz function on the last-row space.

Continuation requires an entire function for every test whose product
with the prescribed pair L-factor agrees with the ordinary integral on
a right half-plane. The function is defined on the entire plane,
including parameters at which the reciprocal Gamma denominator vanishes.
The pair denominators are `realPairLFactor` and `complexPairLFactor` for
the specified parameter lists. The analytic assertion is the ordinary
case of Jacquet's Theorem 2.1(ii), applied to the integrals (2.4) and
(2.6), on p. 6 of the author's version.

Generation is stated for irreducible standard modules with nonzero
Whittaker models. The normalized values are required to cover every
spectral point. At adjacent and equal ranks and for the standard
additive characters `a = ±1`, the stronger conclusion asks for a finite
sum of normalized values equal to one. Each summand uses two individual model vectors. A scalar
coefficient can be absorbed in one Whittaker vector. The supplied
lemma derives pointwise coverage from the finite sum.

The finite-sum assertion comes from Jacquet's Theorem 2.7, p. 10, by
expanding each algebraic tensor. The large-gap assertion additionally
requires the continuous integral maps of Theorem 2.3, pp. 8–9, and the
surjectivity of Theorem 2.6(i), p. 9. Its proof must compare the library
models with Jacquet's smooth coefficient models and justify passing
from the ordered induced model to the supplied irreducible model. The
normalized evaluation at a given point must be continuous on the
completed tensor product. Density of finite sums of compact-finite
pure tensors then gives the required test. Remark 2.2, pp. 7–8, gives a
nonvanishing exponential factor under change of additive character,
which preserves the existence of a nonzero normalized value at each point.
The supplied quotient Haar measures may differ by a nonzero scalar,
which can be absorbed into a coefficient vector for the generation
assertions.

The source is H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
registered as `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
This module states the local assertions. The finite-sum implication is
proved. Model comparison, continuation and generation are proof obligations.
