# Principal parts and polynomial curves

Author: Worker 1478.

This module implements the highest-degree coefficient argument in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Lemma B.1.7, implication (1) to (2), printed pp.563–564, one-based PDF
pp.589–590. The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

The definition `HasAnisotropicPrincipalPart f` says that the sum
`∑ i, (f i).leadingCoeff * b i ^ (f i).natDegree` vanishes only for the
zero vector `b`. Here `f` is an arbitrary family of univariate polynomials
over a field `k : Type u`, indexed by a finite type `ι : Type v`.
The field and index universes are independent.

The theorem
`exists_principalPart_zero_of_sum_comp_eq_zero_of_positive` treats
coordinate polynomials of positive degree over any field. It takes the
maximum degree among their compositions with a nonconstant polynomial
tuple. Retaining the leading coefficient of each tuple coordinate that
attains this maximum, and setting the remaining coordinates to zero,
gives a nonzero vector. The coefficient of the maximum-degree term in
the zero sum of compositions proves that this vector is a zero of the
principal part.

The theorem `exists_principalPart_zero_of_sum_comp_eq_zero` allows zero
coordinate polynomials, assuming that every coordinate polynomial has
zero constant coefficient. If some coordinate polynomial has degree
zero, it is zero, and the vector supported only at that coordinate is a
nonzero principal zero. Otherwise the positive-degree argument applies.
The hypothesis on constant coefficients also ensures that a zero
coordinate of the vector contributes zero, including when the polynomial
itself is zero and its natural degree is zero.

The two theorems in the `HasAnisotropicPrincipalPart` namespace apply this
result by contradiction. Under that anisotropy condition, a polynomial
tuple in the zero locus has every coordinate of natural degree zero;
the tuple therefore equals the tuple of constant polynomials determined
by its constant coefficients.

The provenance is derived. CGP works in positive characteristic with
additive polynomials and group-scheme coordinate isomorphisms. Its
highest-degree argument uses only the separated-variable polynomial
identity. The present algebraic formulation proves that argument for
arbitrary coordinate polynomials, over every field, and explicitly
handles zero coordinate polynomials. It neither constructs coordinates
for a scheme morphism nor identifies arbitrary group kernels with this
polynomial zero locus. In particular, it does not prove the converse
implications of CGP B.1.7 or its requirement concerning every coordinate
isomorphism.

Group-scheme classification, coordinate presentations of arbitrary
groups, central-subgroup extraction, the woundness equivalence and the
host rational-lifting theorem remain open.
