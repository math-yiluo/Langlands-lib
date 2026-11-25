# Reduction of the identity-component clopen theorem

This module proves a conditional reduction, retaining three explicit
prerequisite propositions. It does not prove the unconditional
`IdentityComponentClopenStatement`.

`IdentityComponentClopenReductionStatement` is the implication from these
three explicitly retained propositions to
`IdentityComponentClopenStatement`, uniformly in universe `u`:

- `ReductiveFiberAffinenessStatement`;
- `ReductiveMonomorphismClosedImmersionStatement`;
- `RelativeIdentityComponent.ClopenQuotientStatement`.

`identityComponentClopenReduction` proves this implication. Given the
relative identity component `i : H → G`, its open immersion and the
smoothness and separatedness of `G → S` give the same two properties for
`H → S` by composition. The residue-fibre bridge
`quasiCompact_of_connectedReductive_residueFibers` gives quasi-compactness
of `H → S` over the arbitrary base. The first retained premise then gives
affineness. The bridge
`isReductive_of_isAffineHom_of_connectedReductive_residueFibers` supplies
`IsReductive H` with the exact geometric-fibre convention of the Library.

The second retained premise applies to the underlying monomorphism of
`i`, giving closedness. The ambient hypotheses needed there already
follow from the original target: smoothness supplies local finite
presentation and the target explicitly assumes separatedness and
quasi-compactness of `G → S`.

The third retained premise produces an actual homogeneous quotient `D`.
`RelativeIdentityComponent.exists_etale_fppfQuotient_of_homogeneousQuotient`
then supplies the quotient group, fppf quotient projection, and the
étale/separated/quasi-compact properties required by the exact target.

This is an internal composition of the named Library interfaces and
proofs. It does not discharge the three premises. It adds no stronger
ambient affineness, base separation or base finiteness assumption.
