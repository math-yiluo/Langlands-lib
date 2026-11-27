# Polynomial restriction under transverse derivations

Work over a field of characteristic zero with finitely many variables.
Give the variables weight zero or one, with weight zero for the variables
retained under restriction. For each weight-one variable, suppose a
derivation annihilates the polynomial. Along the coordinate subspace its
coefficient on that variable is a nonzero polynomial in the retained
variables, and its coefficients on the other weight-one variables vanish.
`InvariantPolynomialRestrictionStatement` asserts that a polynomial
satisfying these hypotheses and vanishing on the coordinate subspace is zero.

The proof takes the lowest nonzero weight component of a polynomial
whose restriction vanishes. This component has positive weight. A
derivation is a sum of its coefficients on the variables times the
partial derivatives. The only part that lowers the weight is the
specified multiple of one normal partial derivative. The next lower
component of the equation therefore forces that partial derivative of
the lowest component to vanish. Some normal variable occurs in a
nonzero monomial of the lowest component. Differentiating in that
variable contradicts the nonzero coefficient in characteristic zero.

This criterion gives the polynomial restriction step for injectivity
of the Harish–Chandra projection by the associated graded algebra.
In a Cartan and root-vector basis, the infinitesimal coadjoint action of
an opposite root vector differentiates transversely to the Cartan. Its
coefficient on the paired root variable restricts to the corresponding
nonzero Cartan bracket. The weight-zero restriction of its coefficients
on the other root variables is zero by the root-space bracket rule.
