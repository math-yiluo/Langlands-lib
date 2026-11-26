# Closed adelic conjugacy classes with separable rational characteristic polynomial

`adelicRationalConjugacyOrbit_eq_charpolyFiber` identifies the full adelic conjugacy
class of a rational matrix with separable characteristic polynomial with the fiber of
that polynomial in the adelic matrix group. `isClosed_adelicRationalConjugacyOrbit`
proves that this fiber is closed in the units topology.

At each completion, equality of the characteristic polynomials gives a conjugator
from `regularCyclicBasis` and `cyclicBasis_conjugator`. To choose integral conjugators
at almost every finite place, the proof starts from a rational Bézout identity for
the characteristic polynomial and its derivative. The coefficients of the two
Bézout multipliers are integral at almost every finite place, because a rational
number defines a finite adele and the polynomials have finite support. Both matrices
also have integral entries at almost every finite place. At such a place, injectivity
of the valuation ring inclusion lets the proof read the characteristic polynomial
identity and the Bézout identity over that ring. The reduced matrices then have
separable characteristic polynomial over the residue field. A lift of a residue
cyclic vector has a cyclic-basis determinant with nonzero residue, hence a unit.
The resulting conjugator and its inverse are integral.

`FiniteAdelicGL.fromRestrictedProduct` assembles the finite conjugators, and
`Matrix.piRingEquiv` and `MulEquiv.piUnits` assemble the infinite ones. The other
fiber inclusion follows from invariance of the characteristic polynomial under
conjugation. The coefficient maps are continuous by
`SigmaLiftCharacterIdentity.continuous_charpoly_coefficient`, so the fiber is an
intersection of closed coefficient fibers.

`isClosed_normOneRationalConjugacyOrbit` restricts this result to positive rank
and the determinant-norm-one group. The determinant norm of a positive central
scalar is its parameter to the power `n * [F : ℚ]`. The proof uses the positive
root of the determinant norm of a conjugator to divide out a central scalar.
This preserves conjugation and realizes the orbit inside the norm-one group as
the preimage of the full adelic orbit.

The norm-one comparison follows the positive scalar factorization in Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), §2.6, printed pp. 68–69.
Closedness here supplies the orbit hypothesis of Theorem 18.2.5, printed p. 479,
for the rational separable classes used in §18.4. The retained source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
