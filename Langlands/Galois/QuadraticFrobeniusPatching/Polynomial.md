# Characteristic polynomials of powers

These polynomial identities implement the change in Frobenius eigenvalues
under restriction. For an endomorphism over an algebraically closed field,
`charpoly_pow` proves that taking its \(d\)-th power raises every
characteristic root to the \(d\)-th power with multiplicity.

The proof chooses a finite basis and triangularizes the matrix. An eigenvector
gives the first basis vector through the Library's one-step change of basis.
Induction triangularizes the remaining diagonal block. The diagonal entries
of a power of the resulting upper triangular matrix are the corresponding
powers of the original diagonal entries. The characteristic polynomial of
each triangular matrix is the product of the associated linear factors, and
conjugation preserves the characteristic polynomial of every power.

The roots of `frobeniusRootPower d P` are the multiset of \(d\)-th powers
of the roots of `P`. Mapping powers twice therefore multiplies the exponents.
Over an algebraically closed field the cardinality of the root multiset gives
the degree, which is retained by the operation. The last lemma cancels
polynomial reversal when the degrees agree, by using the same involution
`Polynomial.reflect` on both sides. The arithmetic argument uses this to
recover characteristic polynomials from Euler polynomials at the given rank.
