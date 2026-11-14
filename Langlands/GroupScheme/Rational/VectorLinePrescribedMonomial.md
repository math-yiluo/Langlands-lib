# Prescribed monomial degrees in natural line coordinates

This internal construction chooses the nonzero scalar of an actual epimorphic
equivariant map between naturally coordinated vector lines. The acting torus is
split, the source weight is nonzero, and the source line and torus are affine.
The scalar is the unit supplied by the characteristic-power polynomial theorem.

If the target character is a specified natural-number multiple of the source
character, that specified integer is the polynomial degree. The proof compares
the two character equations after embedding the split torus character lattice
in its rational span. Nonzero source weight allows cancellation. Evaluating the
resulting polynomial identity over every coefficient algebra and applying the
all-test transfer lemma proves the formula on every scheme test. The chosen
field unit precedes the test scheme and its point, and its coefficient is the
pullback along the structure morphism of that test scheme.

This derives only a coordinate formula from the supplied actual epimorphic map,
equivariance, and character equation. It makes no new existence assertion about
root representatives or their images.

The standard additive-group corollary presents the formula as equality of actual
`scalarPoint` morphisms. Auxiliary equivariance lemmas express an arbitrary
supplied additive parametrization's scalar conjugation law as equivariance of
the whole line. A commuting restriction square inherits this law by canceling
the monic target representative after applying the ambient map. Character
pullback is identified with restriction of the actual scalar action. These
steps retain every scheme test and do not impose a normalization on either
supplied parametrization.

The final auxiliary corollary composes this formula with the supplied target
representative. Its hypotheses are the epimorphic restriction, the monic target
map, the commuting squares and a prescribed character multiple. Thus its
conclusion is an equality of the two ambient-group points with the same field
unit and structural coefficient pullback.

`IsTorusEquivariant.weightAction_comp` is reused from [MonicRootParametrization](MonicRootParametrization.md). Unfolding `AutomorphicAction.conjugation_act` gives the product-and-inverse formula used in the restriction square.
