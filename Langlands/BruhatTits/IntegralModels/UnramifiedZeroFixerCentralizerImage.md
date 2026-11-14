# The full residue centralizer in zero-fixer comparison images

This internal supporting construction uses the actual integral split torus in a
smooth unramified zero-fixer model. All objects have arbitrary universe `u`.

For integer-valued building data, a point of the actual centralizer acts on the
apartment by the specified translation. The proved apartment injection shows that
fixing one apartment point forces that translation to vanish. The point then
fixes every apartment subset. Consequently, the preimage of the pointwise fixer
in the actual centralizer is the same for any two nonempty apartment subsets.

`unramifiedZeroFixerCentralizerModel` reuses the published smooth closed integral
torus centralizer inside the supplied target model. Its generic group is the
specified actual centralizer of the apartment torus. The actual special-fibre map
represents the full centralizer of the actual residue torus, on every test
scheme, by base change of integral representability and
`torusCentralizer_baseChange`.

Given two supplied models with integral points described by the same zero datum
and apartment subsets, `unramifiedZeroFixerCentralizerLift` constructs an actual
compatible map from the target centralizer model into the second model. Only the
target is required to be smooth and only its apartment subset is required to be
nonempty. The target centralizer's integral points have ambient images in the
common zero subgroup and fix one target apartment point, hence fix the second
subset. The proved strictly Henselian smooth Hom extension theorem constructs
the lift over the actual maximal-unramified integer ring.

For any compatible generic-identity comparison from the second model to the
target, generic rigidity forces the composite lift to equal the original
centralizer inclusion. This identity persists under the actual residue base
change. Factoring the comparison through its schematic image therefore proves
that its closed image contains the full residue centralizer as a subgroup
functor on every test scheme. The schematic-image statement assumes the
comparison map is quasi-compact; the integral lift and factorization do not.

The provenance is internal composition of the named Library constructions and
theorems. No new literature translation is asserted. This unit proves centralizer
containment. Parabolicity, exact root support and the host facet-order bijection
remain further obligations.
