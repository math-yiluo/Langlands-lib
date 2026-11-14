# Faithfulness of the action of an fppf quotient by the full centre

Worker 683.

This is an internal supporting development for the arbitrary-base quasi-split
inner-form theorem. It derives its results from the published definitions of
`RelativeRoot.IsFppfQuotient`, `center`, `AutomorphicAction.restrict`,
`AutomorphicAction.conjugation` and `AutomorphicAction.IsFaithful`. It introduces
no source-dependent definitions or new assumptions.

For any scheme `S`, group schemes `G` and `Q` over `S`, and an fppf quotient
`q : G ⟶ Q` whose full scheme kernel has range `center G`, the main theorem
`AutomorphicAction.isFaithful_of_isFppfQuotient_center` says that a supplied action
`a : AutomorphicAction Q G` is faithful if its restriction along `q` equals
conjugation on `G`. Faithfulness detects equality of acting points by their
actions after every refinement of their test scheme. There are no reductivity,
affineness, connectedness or nonemptiness assumptions.

`FppfQuotientPointLift q x` records a covering test object, its projection to
the test of `x`, a point lifting `x`, their commutative square, and flatness,
surjectivity and local finite presentation of the projection. The construction
`fppfQuotientPointLift q x` takes the actual scheme pullback along `q` and
supplies these data. This defined construction is the entry declaration.

The helper `hom_ext_of_fppf_local_quotient_lift` uses that construction to test
equality of maps after lifting a quotient point. The projection is flat,
surjective and locally of finite presentation, so
Mathlib supplies an effective epimorphism and hence an epimorphism. Equality
after this projection implies equality on the original test scheme. This is the
fppf analogue of the published fpqc helper
`AutomorphicAction.hom_ext_of_local_quotient_lift`; it requires local finite
presentation rather than quasi-compactness.

`act_lift_of_restrict_eq_conjugation` computes the action of a lifted point.
For `kernel_trivial_of_isFppfQuotient_center`, locally lift an acting point with
trivial action to a point `h` of `G`. The restriction equation implies that
conjugation by every restriction of `h` fixes every group point. Thus `h`
belongs to the all-test centre. The full-kernel equality sends it to the identity
in `Q`. The local-lifting helper gives the identity on the original test scheme.
Finally, the existing `AutomorphicAction.isFaithful_of_kernel` turns kernel
triviality into faithfulness by applying it to the ratio of two acting points.

The proof generalizes the published field-only
`IsAdjointQuotient.innerAction_kernel` and
`IsAdjointQuotient.innerAction_isFaithful`. It constructs neither the quotient
nor its action and does not prove existence of an inner form.
