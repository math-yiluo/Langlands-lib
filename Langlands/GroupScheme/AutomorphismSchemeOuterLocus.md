# The inner action classifier from its outer identity fibre

This internal construction relates two supplied interfaces over every base
scheme: a full `GroupIsomorphismScheme G G`, and an
`OuterIsomorphismScheme I a` for an arbitrary automorphic action `a`.
It assumes both representatives and proves no representability existence.

The represented automorphism group has a global identity point.
`identityPoint` is that point in the unchanged Isom parameter, and its
universal automorphism is the identity on every relative test.
The action classifier in `I.toGroupAutomorphismScheme` evaluates to the
given action on every test.

The outer orbit uses inverse precomposition. Consequently its orbit
through `identityPoint` classifies the inverse of the acting point.
`inv_comp_identityOrbit` proves that precomposing this orbit with the actual
categorical inversion morphism equals the direct action classifier.
The proof compares universal automorphism evaluations on every refinement
and uses that inversion is an involution.

The global orbit construction identifies this orbit with its actual outer
fibre. It is open when the outer parameter is étale over the base and closed
when the parameter is separated. Inversion is an isomorphism, so the same
properties hold for the direct action classifier. No reductivity,
connectedness, affineness or nonemptiness hypothesis is needed for these
conditional conclusions.
