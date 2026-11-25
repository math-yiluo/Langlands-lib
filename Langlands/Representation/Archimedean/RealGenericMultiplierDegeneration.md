# Exact binomial and canonical-tail degenerations of generic multipliers

This module identifies two scalar specializations of the
finite-product generic multipliers in the Library. Its inputs are
`RealBlockMultiplier` and the published analytic pole-removal construction
`RealBlockMultiplierNormalization`. No external literature assertion is used.

Let ell>0, let eps be 0 or 1, and suppose ell−1−eps is even. The binomial base
value B=`binomialSeq ell eps 0` is nonzero. For every integer j,

`binomialMultiplier ell eps j = B * genericMultiplier ell eps j`.

The generic coordinate is analytic at the positive parameter ell. Thus the
binomial is exactly its positive resonant value, with the displayed scalar
normalization, including all negative-index reflection signs.

Write ell=eps.toNat+2r+1. The pole-removal construction defines
`regularizedSeq` and `regularizedMultiplier` by removing the denominator
factor eps+2r+1+nu before evaluation at nu=−(eps+2r+1). Put
T=`regularizedSeq (-(eps+2r+1)) eps r (r+1)`. This scalar is nonzero, and
for every integer j the regularized multiplier at that negative pole equals

`T * tailMultiplier ell eps ((-1)^eps.natAbs) j`.

Each regularized coordinate is analytic at the pole. The symmetry here is
`(-1)^eps`, the sign-preserving canonical tail symmetry on the resonant
parity class. The differential tail symmetry `(-1)^ell` is different.

`RealGenericMultiplierDegenerationStatement` packages these two normalized
identities, the nonzero scalars, and the coordinatewise analyticity claims.
`realGenericMultiplierDegeneration` proves it.

The positive identity follows by induction on the nonnegative sequence index.
Both the binomial sequence and the generic sequence obey the same recurrence,
and its denominator is nonzero at the positive parameter. Their initial
values fix the scalar B. The binomial support criterion proves B is nonzero.

For the negative pole, the published regularized sequence is zero through
index r, as is the tail sequence. At r+1 the tail sequence equals one, fixing
the scalar T. Above r the regularized and tail recurrences agree and have
nonzero step denominator. Induction proves the equality at every sequence
index. The published pole-support criterion makes T nonzero. Extending both
sequences by the same reflection sign proves the multiplier identities for
all integer indices. Coordinatewise analyticity follows from the published
finite-product and erased-product formulas.

These are scalar identities. This module constructs no rational operator family,
limiting intertwiner, braid relation, or GL4 kernel-image or filtration proof.
Such uses require a common finite compact space and justified propagation of
an operator identity to the indicated specializations.
