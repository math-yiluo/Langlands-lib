# Affine coefficient parameters for conjugation

This internal construction is derived from `CorepresentedNormalizer` and
`ProjectiveTensorCoefficients`. For an affine group represented by an algebra
`B`, let `I` cut out a subgroup and suppose that `B/I` is projective over the
base ring. The parameter algebra is the polynomial algebra with a variable for
each pair consisting of an element of `B` and a linear form on `B/I`.
Its map to `B` sends a variable to the corresponding contraction of the
universal conjugation map.

The implemented proof first uses dual contractions to compare base changes of
tensors. Polynomial algebra maps agree precisely when they agree on every
variable, so equality of the coefficient parameters is equality of the two
universal conjugates. The group identity for two conjugates then identifies
each fiber with a right coset of the centralizer family. This assertion uses
all algebra extensions and permits arbitrary, nonflat test algebras.

The relative spectrum of this polynomial algebra is the affine parameter
scheme `conjugationCoefficientScheme`. The algebra map induces the actual
scheme morphism `conjugationCoefficientOrbit` from the corepresented group
to that scheme. Relative Spec adjunction naturality identifies equality after
this morphism with the preceding coefficient equality on relative global
sections, for every scheme test.

For a subgroup inclusion `j`, the scheme-level fiber theorem assumes that the
ideal `I` cuts out its full range on every scheme test, expressed using
`Corepresented.pointsEquiv`, and that `B/I` is projective over `R`.
The published cut-out centralizer comparison identifies centralizer membership
on a scheme test with membership in the algebra centralizer family on relative
global sections. The algebraic fiber theorem and the multiplicativity of
`pointsEquiv` then show that two scheme points have the same orbit parameter
if and only if their ratio `g⁻¹ * h` belongs to the full centralizer of the
represented subgroup. The theorem uses arbitrary scheme tests and all their
refinements through the centralizer functor.

No smoothness or finite-generation assumption is used here. The parameter
algebra can have infinitely many variables. This construction supplies an
exact-fiber map; it does not itself construct a quotient or descend that
quotient to an arbitrary base scheme.
