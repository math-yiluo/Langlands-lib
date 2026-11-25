# Central infinitesimal uniqueness for groups of multiplicative type

The universal property of the ideal quotient gives the affine test schemes
used in the reduction to diagonalizable action rigidity.

`quotientTest` gives an affine test algebra annihilating `I` the actual
structure of a scheme over `Spec (R/I)`. `quotientTest_comp` identifies
the composite structure morphism to `Spec R`.

`eq_on_test_of_pullback_map_eq` constructs a point of the pullback from
a test whose structure morphism factors through the new base.
Composing the pulled-back equality with this point and the projection
gives equality on the original test. `action_trivial_on_quotient_test` applies this to an
action morphism and the second projection. It supplies precisely the
affine-test triviality hypothesis of `DiagonalizableActionRigidityInput`.

`diagonalizable_central_uniqueness` applies that input to the actual
left-right action of two homomorphisms with the same central reduction.
`isDiagonalizable_central_uniqueness` transports the result along any
relative diagonalizable presentation, using the published comparison
with the integral split model. The argument applies to arbitrary target
group schemes.

`multiplicativeType_central_uniqueness_of_actionRigidity` treats the
full relative multiplicative-type source. Choose an affine chart of its
fppf splitting cover through each base point. Extend the ideal to each
chart algebra. Nilpotence, equality of the two reductions, and centrality
of their common reduction persist under this base change.
Apply the diagonalizable result on that chart, then use the published
pointwise fppf equality criterion to descend equality to the base.

The published `SchemeAction.hom_eq_snd_of_nilpotent_quotient` proves
`DiagonalizableActionRigidityInput` for arbitrary scheme targets.
`centralInfinitesimalUniqueness` applies that result to the reduction
above. Thus two homomorphisms from a group of relative multiplicative
type into an arbitrary group scheme over `Spec A` are equal when their
reductions modulo a nilpotent ideal agree and the common reduction is central.
