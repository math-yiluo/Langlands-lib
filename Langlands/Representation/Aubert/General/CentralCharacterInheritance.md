# Full-center character inheritance

This is an internal deduction from the published actual representation
constructions. It supplies no new external representation-theoretic assertion.
Throughout, a unitary central character is a character of the full abstract
group center, with open kernel, norm one, and the stated scalar action.

`Langlands.UnitaryCentralCharacter.pullbackInjective` retains the same character
and all its topological and modulus data along an injective intertwining map.
Intertwining and linearity identify the images of the desired scalar-action
identity, and injectivity proves the identity. The dual construction
`pushforwardSurjective` chooses a preimage and proves the scalar identity by
intertwining and linearity. Neither construction requires a nonzero carrier.
The source and target vector-space universes are independent.

`restrictSubrepresentation` and `descendQuotient` apply these constructions to the
literal invariant subspace and module quotient in
`Langlands.Representation.Category.Subquotients`. Their maps and injectivity or
surjectivity are the published `SmoothRep.subtype`, `subtype_injective`, `mkQ`,
and `mkQ_surjective`. Thus the resulting character acts on the actual objects,
without choosing isomorphic replacement representations.

For the remaining results the ambient group is locally compact and
nonarchimedean. The subgroups, their closedness and normalization conditions,
and the containment of the full ambient center in the Levi remain explicit.
The map `ambientCenterToLeviCenter` is the literal ambient central element viewed
in the full Levi center.

`norm_inducingScalar_ambientCenter_eq_one` assumes a supplied unitary central
character on the actual normalized induction and a scalar character on the
inducing representation. The published
`normalizedInductionCentralCharacter_acts` identifies the action of an ambient
central element with the inducing scalar. On a nonzero induced vector,
comparison with the supplied central action and scalar cancellation identify
the two character values. The unit norm of the latter gives the conclusion.
Nontriviality of the actual normalized induction is an explicit hypothesis.

`normalizedJacquet_ambientCenter_acts` proves that the supplied ambient central
scalar acts unchanged on the actual normalized Jacquet module. Every quotient
vector has a representative by `Jacquet.Localization.mk_surjective`.
`normalizedJacquetFunctor_obj_apply` expresses the action on its class. The
published `closedHalfCharacter_eq_one_of_mem_center` makes the inverse
normalizing factor one, because the element is central in the ambient group.
The original scalar identity then descends through the linear quotient map.
This action identity also covers the zero Jacquet module.

`norm_jacquetScalar_ambientCenter_eq_one` compares that action with any supplied
scalar character of the full Levi center on a nonzero normalized Jacquet
module. Scalar cancellation on one nonzero quotient vector identifies its
value on each ambient central element with the original unitary character
value. Nontriviality of this Jacquet module remains explicit.

These results transport supplied data and compare scalar actions. They do not
establish admissibility, scalar-character existence, nonvanishing, unitarity of
the entire inducing character, or the rank-one self-association theorem. They
use no classification, character independence, geometric lemma, adjointness,
or cuspidal-support theorem. Their direct dependencies are
`InductionCentralCharacter` and `Category.Subquotients`, with the actual
normalized induction and Jacquet constructions imported by the former.
