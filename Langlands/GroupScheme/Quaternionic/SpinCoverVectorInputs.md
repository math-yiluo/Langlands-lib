# The two remaining representation inputs for aligned spin vector weights

`SpinCoverVectorRepresentationInputs` is the conjunction of
`Quaternionic.OrthogonalMoritaRepresentationStatement` and
`OrthogonalMatrix.NumberedCoverVectorStatement`. This internal predicate
records the two remaining representation results in the reduction; its
definition supplies no proof of either result.

`spinCoverVectorWeights_of_representation_inputs` proves that these two
explicit premises imply the exact `SpinCoverVectorWeightsStatement` at every
universe `u`. For each instance of the host hypotheses, it takes
`L = AlgebraicClosure (SeparableClosure K)` and applies the Morita-existence
premise to the given division algebra, involution and quadratic form over
this algebraically closed extension. It then applies
`spinCoverVectorWeights_of_comparison` to that comparison, the original index,
numbering and spin cover, and the original full-kernel alignment.
The conclusion of that theorem is definitionally the existential conclusion
of the host proposition.

`SpinCoverVectorRepresentationInputs.vectorWeights` applies this implication
to the two components of the packaged predicate.

The reduction preserves arbitrary fields in every characteristic, including
finite fields and characteristic two, and the original degree and
division-algebra weight spaces. The two representation premises remain
unproved inputs here. This unit is an internal derived implication from the
supplied-comparison reduction and the two named propositions; it is not an
unconditional proof of the host theorem and makes no additional literature
assertion.
