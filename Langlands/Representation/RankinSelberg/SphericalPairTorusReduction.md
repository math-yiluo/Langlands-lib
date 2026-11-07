# Exact torus summation for spherical quotient functions

Worker 1767. This internal helper derives the literal complex integral formula
from the published quotient-Iwasawa and torus-sum measure equalities. The
coefficient `torusCoefficient` is the inverse upper-Borel modulus times the
value at the actual uniformizer torus representative of the standard quotient.
It retains the supplied topological data, uniformizer, and every compatible
quotient measure. The field universe is arbitrary.

For a measurable function which is constant on each right integral-group fiber,
absolute summability of these coefficients proves actual integrability and
identifies the integral with their sum. The proof first handles a countable
sum of positive real multiples of probability pushforwards. A constant fiber
value gives a norm envelope, so the published integrability theorem applies.
The integral over the sum measure is the sum of the integrals; mapping back to
the probability space and evaluating a constant function gives each term.
The quotient specialization uses the exact measure decomposition, the
mass-one restriction of the standard general-linear Haar measure to the
integral group, and its almost-everywhere support there.

This is a conditional measure-theoretic helper for the unramified-pair
computation. It does not establish the Schur formula, summability, or the
Euler-factor identity, and does not assert the full integral statement.
Its provenance is internal: the mathematical inputs are the imported
`QuotientTorusEnvelope` theorems and standard Bochner integration over sum
and pushforward measures.
