# Radical extension through a supplied smooth quotient

This internal derived result combines represented radical preimages with
preservation for smooth connected affine groups. Let `k → K` be an arbitrary
extension of algebraically closed fields in universe `u`. Suppose
`q : G → Q` is smooth, scheme-surjective and quasi-compact, with `Q` smooth,
connected and affine. Assume that the actual scheme-theoretic kernels of both
`q` and its actual base change are smooth, connected and unipotent, using the
existing all-test fixed-vector predicate.

`IsUnipotentRadical.baseChange_of_isAlgClosed_of_smooth_quotient` proves that
the actual base change of any supplied represented radical of `G` is a
represented radical. There is no affineness premise on `G`, its radical, or the
kernels. Existence of `q` and the two kernel predicates are explicit inputs.

The proof chooses a represented radical `j` of `Q` using affine radical
existence. The radical-preimage theorem identifies the supplied radical's
all-test image with the full inverse image of the image of `j`.
Affine radical preservation makes the actual base change of `j` a radical
of the base change of `Q`. The radical-preimage theorem over `K` then makes
its full inverse image a radical. Images of homomorphisms and inverse images
of subgroup functors commute with the actual base-change functor, so this
inverse image has exactly the all-test image of the original radical's base
change.

The auxiliary `IsUnipotentRadical.of_range_eq` transfers the complete radical
predicate to any closed representative with the same all-test image. It
constructs the actual source isomorphism using
`IsClosedSubgroup.sourceIsoOfRangeEq`, then uses its inclusion equation and
`IsUnipotentRadical.precomp_iso`. Applying this transfer finishes the proof,
including the full greatestness property. It does not require an independent
base-change theorem for unipotence of nonaffine groups.

`SmoothUnipotentQuotient.radicalBaseChangeIso` compares the actual base change
of the original radical source with any supplied radical representative over
`K`. Its `radicalBaseChangeIso_hom_comp` theorem states that the isomorphism
followed by the supplied inclusion is the original base-changed inclusion.

All ingredients are internal deductions from the existing radical predicates,
affine radical existence and preservation, radical-preimage geometry, and
all-test subgroup comparison. This conditional prerequisite does not establish
existence of the quotient or preservation for arbitrary smooth ambient groups.
