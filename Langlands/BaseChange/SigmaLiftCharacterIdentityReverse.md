# From Shintani lifts to σ-lifts

`SigmaLiftCharacterIdentityReverseStatement` gives the reverse implication of
`SigmaLiftCharacterIdentityStatement` with the same fields, representations and constant.
It takes `ConcordantIntegrableIntegralEqualityStatement`,
`CharacterLocalIntegrabilityStatement` and `TwistedCharacterLocalIntegrabilityStatement`
as premises.

The two local integrability statements supply functions representing the ordinary and
twisted distributions. On the respective regular sets their point values are local
character values. Conjugation preserves the characteristic polynomial, so uniqueness of the
ordinary local value makes the ordinary function constant on each regular conjugacy class.
Every twisted conjugate of an associated element is associated with the same ordinary
element. The Shintani identity and uniqueness give the same twisted character value there
as the ordinary value scaled by the Shintani constant.

Multiplying any concordant pair by these weights preserves concordance. The two products
are integrable by continuity and compact support of the test functions and local
integrability of the weights. The integral comparison identifies the two product integrals.
Taking the constant outside the ordinary integral yields the required distribution identity
for every Haar pair.

The reduction implements the first implication in the proof in Henniart–Lemaire 2011,
II.2.11, printed p. 72. Its premises express the characteristic-zero character integrability
results and the consequence of the two Weyl formulas needed for the comparison.
