# Central infinitesimal uniqueness from diagonalizable action rigidity

Worker 890.

This internal construction factors affine test schemes through an ideal
quotient and reduces central infinitesimal uniqueness to the explicit
`DiagonalizableActionRigidityInput` proposition.

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
with the integral split model. The target group scheme is arbitrary;
no affineness or smoothness hypothesis is used.

`multiplicativeType_central_uniqueness_of_actionRigidity` treats the
full relative multiplicative-type source. Choose an affine chart of its
fppf splitting cover through each base point. Extend the ideal to each
chart algebra; its nilpotence, equality of the two reductions, and
centrality of their common reduction persist under this base change.
Apply the diagonalizable result on that chart, then use the published
pointwise fppf equality criterion to descend equality to the base.
The resulting conclusion has exactly the quantifiers and hypotheses
of central infinitesimal uniqueness for arbitrary target group schemes.

The action-rigidity proposition remains an explicit hypothesis. This
module does not assume its unpublished proof and does not yet assert
unconditional central infinitesimal uniqueness.
