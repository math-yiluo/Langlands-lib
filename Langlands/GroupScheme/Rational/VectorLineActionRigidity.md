# Actions between vector groups of dimension one

This internal auxiliary result for normal-root centralization constructs the
universal coordinate polynomial of an actual automorphic action and proves that
the action is trivial. The field, its characteristic, and its universe are
arbitrary. Both the acting group and the group acted on must be vector groups
of dimension one in the published all-test sense.

`VectorLineAction.coord` and `point` identify affine points with one element of
their coefficient algebra. These identifications are inverse and commute with
every coefficient-algebra map when the supplied vector coordinates are natural.
`actionCoord` writes the given action in these coordinates.
`actionPolynomial : k[X][X]` evaluates it at the universal pair: the inner
variable is the acting parameter, and the outer variable is the point acted on.

The implemented proof uses polynomial inverses, rather than a classification of
additive polynomials. Naturality under substitution in the outer variable and the
inverse-action law give
`q.comp p = X`, where `p` is the universal action polynomial and `q` uses the
negative acting parameter. Over the integral domain `k[X]`, multiplication of
degrees forces both polynomials to have degree one. Both vanish at the origin,
so they are scalar multiples of the outer variable. Their scalar coefficients
multiply to one. Units of `k[X]` are constant, so `p = C (C c) * X` for some
`c : k`. Specializing the acting parameter to zero and using the identity-action
law gives `c = 1`, proving `actionPolynomial_eq_X`.

Evaluation of this polynomial in an arbitrary commutative coefficient algebra
proves `actionCoord_eq` and `affineAct_eq`; the algebra may be nonreduced.
The published affine-test morphism extensionality lemma, proved using an affine
open cover, extends the equality to every relative test scheme.
`VectorLineAction.eq_trivial` then identifies the actual action morphism with
the second projection. The coordinate-free companion
`AutomorphicAction.eq_trivial_of_vectorLines` requires only the two published
`IsVectorGroupOfDimension _ 1` predicates.

The provenance is internal: the construction combines natural vector coordinates,
the intrinsic laws of an actual automorphic action, standard polynomial degree
and unit lemmas, and affine-test extensionality. No root-group dimension or
preservation theorem is assumed or proved here. Applying the result to normal
root centralization still requires constructing the appropriate automorphic
action on a vector root group of dimension one. The full root dichotomy and
semisimple almost-simple generation remain separate obligations.
