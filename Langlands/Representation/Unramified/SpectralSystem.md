# Finite-exception numerical spectral systems

This internal construction extends the published
`Langlands.Unramified.Eigenvalues` multiset model. It supplies numerical
operations needed to compare supplied unramified data. It does not construct
an automorphic representation, assert a Satake correspondence, or identify a
matrix with arithmetic Frobenius.

`SpectralSystem I n` consists of a finite exceptional set in an arbitrary
index type `I` and a multiset of exactly `n` nonzero complex numbers at each
remaining index. Repetitions in the multiset retain their multiplicities.
There are no values at the exceptional indices. A consumer must separately
prove that the spectra belong to its actual local representations or arithmetic
objects. In particular, this structure alone is not an automorphic realization
or a weak global association.

The rank is a natural number. Positive local ranks are obtained by specializing
it to `r + 1` or the natural value of a positive natural number. Allowing rank
zero also handles an empty finite family without exceptional conventions.
The place and family index universes are independent; the family index type is
any finite type. No equality or cardinality constraint is imposed on ranks in
a comparison.

The numerical power trace and Euler denominator are those of `Eigenvalues`:
the sum of the powers of every eigenvalue and the product of the linear
polynomials `1 - z X`, respectively. Their rank at power zero, constant value
one at zero, nonvanishing, and full polynomial degree are proved by the
published multiset identities. Restriction to a larger exceptional set forgets
data and preserves both invariants at all remaining indices.

`Eigenvalues.finiteSum` concatenates any finite family of varying ranks using
multiset addition. Its cardinality is the sum of the ranks. Induction on the
finite index set proves that power traces add and Euler polynomials multiply.
`SpectralSystem.finiteSum` applies this construction outside the finite union
of the individual exceptional sets. The same formulas therefore hold for the
system. The finite union contains each individual exceptional set by a proved
membership lemma. Repeated family entries contribute repeatedly; they are
never deduplicated as spectra. The resulting system inherits the exact total
degree, nonvanishing and constant value one from the rank-generic laws.

`SamePowerTraces` requires equality of every positive power trace outside
**one common finite exceptional set**, independent of the power. The
cofinite quantifier occurs before the quantifier over positive powers.
`SameEulerPolynomials` requires equality of the Euler denominators outside a
finite set. Their guarded nonmembership arguments refer to the supplied
partial data; they do not extend either invariant by invented values.
Both relations are reflexive, symmetric and transitive, including across
different ranks. Transitivity explicitly discards the middle system's finite
exceptional set before composing equalities. Restricting a system preserves
both relations.

The two final comparison lemmas expand comparison of combined systems to the
literal sums of traces and products of Euler polynomials, allowing different
finite index types and ranks on the two sides. This file does not prove that
the two comparison relations are equivalent. The determinant-polynomial and
positive-trace equivalence in
`Langlands.Automorphic.Unramified.EulerProductTraceStatement` remains a
separate theorem obligation. It is neither imported nor assumed here.
For finite or empty place types the cofinite relations are vacuous, as expected
for “outside finitely many indices”; applications to number fields use their
actual finite places.

All content here is an internal construction from finite multisets, finite
unions and the cofinite filter, with its intrinsic laws proved. No new original
literature claim or theorem truth is postulated. The only project import is
the published `Langlands.Representation.Unramified.Eigenvalues`; the remaining
imports are Mathlib's finite-set and filter APIs.
