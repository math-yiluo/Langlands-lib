# Full-centre containment from a centre-containing split torus

This internal construction restricts every actual automorphic action to any
representative of the full centre. It reuses the published
`AutomorphicAction.isStable_center` from `Adjoint.Action`: stability follows on
every refinement by applying the acting point's group automorphism to
commutation with the inverse image of an arbitrary target point. The
representing inclusion intertwines the restricted action with the original action.

For a normal subgroup of a smooth connected affine group, ambient conjugation
therefore acts on its represented full centre. If that centre embeds as a
closed subgroup of a split torus, the preceding all-test rigidity theorem makes
this action trivial. The inclusion equation for normalized conjugation then
says that every image point of the centre commutes with every ambient point,
after every refinement. Neither the centre nor the test scheme is assumed
smooth or reduced.

Over an algebraically closed field, the trivial-action specialization of
`FixedCenterContainingTorusStatement` supplies a split torus containing the
full centre of a connected reductive group. The published full-centre
representative factors through that torus, and the factor remains a closed
immersion. This gives full-centre containment for a normal connected reductive
subgroup under the stated fixed-torus premise. These are internal deductions
from the published centre representation, normalized conjugation, represented
action, split-torus and group-like rigidity interfaces, in arbitrary universe.
The fixed-torus premise and the host semigroup comparison are not proved here.
