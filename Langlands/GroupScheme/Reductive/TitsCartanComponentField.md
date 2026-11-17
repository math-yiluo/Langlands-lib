# The finite separable field of a full Cartan-component stabilizer

Worker 509. This is derived interface material over arbitrary fields and at
every universe parameter. It uses the published star-action continuity theorem,
the actual Cartan-component stabilizer, and Mathlib's infinite Galois
correspondence. It imposes no new hypothesis on the group or field.

Continuity supplies a finite intermediate field whose pointwise fixer acts
trivially through the star action on the entire root datum. In particular, that
fixer stabilizes the chosen actual Cartan component. Monotonicity of openness
for subgroups makes the component stabilizer open, and an open subgroup of a
topological group is closed.

`cartanComponentField` is the intermediate field fixed by this full stabilizer.
Infinite Galois correspondence shows that its fixing subgroup is exactly the
original stabilizer; it is finite dimensional over the ground field because
the subgroup is open, and separable as an intermediate field of the separable
closure.

`cartanComponentSeparableClosureEquiv` identifies its own separable closure
with the ground field's separable closure, now viewed over this intermediate
field. Separability follows by passing to the top of the scalar tower.
`cartanComponentAbsoluteGaloisEquiv` conjugates automorphisms through that
closure equivalence, applies the fixing-subgroup equivalence, then uses exact
recovery of the stabilizer. It identifies the whole absolute Galois group of
the component field with the whole component stabilizer.

`cartanComponentAbsoluteStarRepresentation` composes that group equivalence
with the original stabilizer's permutation representation on the actual
Cartan component. Both lift lemmas retain one Galois element for every vertex
simultaneously. In the stabilizer-to-field direction the inverse group
equivalence supplies the witness; in the reverse direction the forward group
equivalence supplies an element that also explicitly stabilizes the component.

This representation is defined on the original component. The unit does not
identify it with the star action of an actual factor group, construct a factor,
or claim `SemisimpleTitsComponentFactorStatement`. Those are separate structural
comparison obligations. No local rank-one or Kneser–Tits result is used.
