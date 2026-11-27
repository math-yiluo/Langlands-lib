# Injectivity of Cartan center projection from root-basis data

Give a finite Lie basis weights zero on Cartan directions and one on
root directions. Suppose each root basis direction has a bracket with
some Lie element whose Cartan component is nonzero, and that bracketing
the other root basis vectors with that same element gives zero Cartan
component. Over a field of characteristic zero, a central element
with zero PBW coordinates on all weight-zero monomials then vanishes.

Take a nonzero central element's highest PBW degree. The corresponding
polynomial symbol vanishes on the Cartan coordinates by the
coordinate hypothesis. It is annihilated by coadjoint
derivations because commutation with a Lie generator is zero on a
central element and induces the corresponding derivation on the
symbol. The bracket hypothesis gives the transverse coefficients in
`InvariantPolynomialRestrictionStatement`. That criterion forces the
symbol to vanish, contradicting its nonzero leading coefficient.

For the projection to a split Cartan in a complex reductive Lie
algebra, choose each transverse direction in the opposite root
space. The bracket of the two root vectors is a nonzero multiple of the
coroot, and brackets with the other root spaces have zero Cartan component.
A central element in the kernel of the projection belongs to the
right ideal of positive root directions. With the positive root
letters first in PBW order, the expansion of that ideal in monomials
containing a positive letter gives the coordinate hypothesis.

The Cartan injectivity assertion is part of the Harish–Chandra
isomorphism in Knapp and Vogan, *Cohomological Induction and Unitary
Representations* (1995), Chapter IV §7, Theorem 4.95, p. 286. Their proof of
injectivity on p. 291 uses finite-dimensional matrix coefficients.
The implemented argument proves the basis-level criterion using PBW
symbols and transverse polynomial derivatives.
