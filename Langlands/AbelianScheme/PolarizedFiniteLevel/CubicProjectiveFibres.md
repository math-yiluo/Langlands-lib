# Actual residue fibres of cubic projective evaluation

This internal derived unit restricts the actual cubic projective evaluation
to the actual residue fibres of the original abelian structure map. It retains
positive polarization index, the specified finite local rank of the actual
cubic direct image, and intrinsic generation of its full evaluation.
All schemes have an arbitrary common universe.

`cubicProjectiveEvaluationFibre` is the pullback map from the fibre of the
original abelian structure map to the fibre of the actual cubic projective
projection. The construction uses the proved structure-map equation for
evaluation. Its source is also the underlying scheme of the datum pulled
back along the original base's residue-field point. The two displayed
identities describe its composites with the target fibre inclusion and
the target residue-field projection. `cubicProjectiveEvaluationFibreOver`
packages the latter identity as an actual morphism over the residue field.

Pullback pasting proves that its square with the original evaluation and
the two fibre inclusions is Cartesian. Properness follows by base change
from properness of actual cubic evaluation.

`cubicProjectiveEvaluationFibrePullbackIso` identifies the pullback of the
restriction of the global degree-one bundle with the actual cubic bundle
of the actual pulled-back datum. The implemented isomorphism composes the
fibre square's line-bundle pullback comparison, the original global
evaluation pullback isomorphism, and the already proved canonical
base-change comparison for the cubic bundle. It requires no new choice
of line bundle or compatibility hypothesis.

Finally, actual cubic evaluation is a closed immersion if and only if
each of these actual residue-fibre evaluations is a closed immersion.
One direction is stable base change. For the converse, take the canonical
point above each point of the projective target. Its target fibre
inclusion induces an isomorphism on residue fields because it is
surjective on stalks. The Cartesian target-fibre comparison from
`RelativeFibreClosedImmersion` transfers closed immersion to the original
target residue fibre. The proper target-residue-fibre criterion then
proves closed immersion on the total space.

This unit neither identifies the projective target fibre with the
projectivization of the full direct image on the fibre nor proves
generation, finite local rank, fibre very ampleness, or ordinary moduli
representability. Those remain separate geometric obligations.
