# Functorial normalized integer valuations on separable extensions

This internal construction derives from `HenselianIntegerAddValuation` and
Mathlib's separable closure and normal-extension conjugacy. It extends the
normalization to separable extensions that need not be normal. The base and
extension universes are independent; maps between two extensions can have a
third independent universe. No topology, residue-field, characteristic or
surjectivity assumption is needed.

In a Galois extension, two elements with equal minimal polynomial are carried
to one another by an automorphism. Invariance of
`henselianIntegerAddValuation` proves that their values are equal.
Consequently every embedding of a fixed separable extension into
`SeparableClosure K` gives the same value on each element: the minimal
polynomials of the images equal that of the source element.

`henselianSeparableAddValuation` restricts the normalized invariant additive
valuation on the separable closure along a chosen embedding. The embedding
independence theorem allows computation using any such embedding.
For an algebra embedding from one separable extension to another, compose a
chosen embedding of the target into the separable closure with the given
map. This computes the source value and proves preservation of values.
Automorphism invariance follows as a special case.

Every embedding commutes with the map from the base field. The exact base
normalization is therefore the negative integer logarithm of the supplied
multiplicative valuation.

For a finite separable extension, the norm is the product of the roots of
the minimal polynomial, raised to the degree over the simple subextension.
The polynomial splits in the separable closure. Every one of its roots has
the same minimal polynomial as the embedded element, so invariance gives
equal values. Induction over the root multiset gives its cardinality as
multiplier. That cardinality is the degree of the simple subextension, and
the tower-degree formula produces the total extension degree.
The nonzero norm then has an integer base value; division by the positive
degree proves inverse-degree integer-lattice containment. No surjectivity
onto that lattice is asserted.

This is a field-theoretic prerequisite for coordinate valuations. It supplies
no arbitrary-group relative-root comparison or apartment-existence theorem.
