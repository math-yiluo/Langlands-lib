# Actual affine commutator pullbacks and their identity slices

This internal construction implements the constant-identity-slice part of
CGP, *Pseudo-reductive Groups*, second edition (2015), Lemma 3.3.4,
printed pp.108–109 / PDF pp.134–135. The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`. The coordinate implementation
uses the Library's existing actual affine presentations; it does not assume
the remaining augmentation-weight comparison or geometric generation theorem.

All constructions work over an arbitrary commutative base ring, in an arbitrary
universe. `genericPoint H` is the actual point of H corresponding under
`Lie.pointCoordinates` to the identity of `Lie.coordinateAlgebra H`.
Every affine point is recovered from it by coefficient extension, and
`Lie.coordinateOrigin H` sends it to the identity point.

For actual G-points x over A and y over B, `tensorPoint` forms their
commutator after the independent inclusions into A tensor B.
`tensorPullback` is its coordinate algebra map. Its evaluation theorem
identifies every algebra specialization with the commutator of the two
specialized points. If either specialized input is the identity, this
pullback is the constant identity map. The two identity-slice lemmas use
the standard tensor algebra lift of an augmentation and an identity map;
their proof uses actual point naturality and the group identity
[1,y]=[x,1]=1.

For group-scheme homomorphisms i:H→G and j:K→G, `commutatorHom i j`
is an actual morphism H times K→G. `commutatorHom_apply` describes its
value on every test scheme. The algebra map `pullback i j` is defined by
the two generic points and is proved to evaluate this scheme morphism.
Its left and right identity slices are the constant map obtained from
`Lie.coordinateOrigin G`. This is the geometric input for the separate
augmented-tensor kernel calculation. Neither injectivity of this pullback
nor any torus weight bound is asserted here.
