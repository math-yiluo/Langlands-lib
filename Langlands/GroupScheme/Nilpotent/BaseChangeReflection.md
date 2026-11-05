# Reflection of nilpotence under field base change

This internal helper supplies descent of nilpotence for the Cartan structure
task. Both fields have arbitrary universe `u`, and the actual morphism
`b : Spec K → Spec k` is assumed flat and surjective. No characteristic,
perfectness, separability, algebraic closedness or torus splitting assumption
is used.

`HasUniformNilpotentPoints.of_baseChange` reflects the same natural-number
bound `d` from the pullback group to the original group. Its hypotheses impose
no smoothness, connectedness, affineness or reducedness on the group. The
predicate concerns the `d`th lower central subgroup on every relative scheme
test, including nonreduced tests.

The proof uses the published universal iterated commutator word with source
`IteratedCommutator.source G d`. Pulling this source back along `b` gives a
cover whose projection is an epimorphism, by flatness and surjectivity.
The published multiplicative point equivalence
`baseChangePointsEquiv` transports the assumed lower central bound to points
over the underlying pulled-back source. The universal word evaluated on the
projection lies in this lower central term, so it is the identity.
Cancellation of the epimorphic projection proves that the original universal
word is the identity. The published word-to-bound theorem then supplies the
original all-test bound. Thus descent preserves the specified index `d`.

`hasUniformNilpotentPoints_baseChange_iff` combines this reflection with the
published preservation theorem `HasUniformNilpotentPoints.baseChange`.

`IsNilpotentGroupScheme.descendedUniformNilpotenceBound` assumes the original
group is smooth, connected and affine, and that its field pullback is
geometrically nilpotent. The pullback has the same geometric properties, using
`connectedSpace_baseChange_of_smooth_affine` for connectedness. The published
`IsNilpotentGroupScheme.uniformNilpotenceBound` then supplies a chosen natural
number bound. The new definition retains that number unchanged. Its
`descendedUniformNilpotenceBound_spec` theorem reflects this bound and proves
it valid on every relative scheme test of the original group.

`IsNilpotentGroupScheme.of_baseChange` applies
`HasUniformNilpotentPoints.isNilpotentGroupScheme`
to this specification to obtain geometric nilpotence of the original group.
The final equivalence also uses the published forward
theorem `IsNilpotentGroupScheme.baseChange`.

The provenance is internal: these are consequences of the existing point
equivalence, universal commutator construction, flat epimorphism theorem and
uniform nilpotence results. This pair proves a descent step. It does not
establish nilpotence of a Cartan after field extension, geometric maximality
of its witnessing torus, or the full `CartanStructureStatement`.
