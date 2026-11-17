# Unipotent extensions and radical preimages without affine sources

This derived module removes affine-source and affine-kernel assumptions from
the published extension and radical-preimage arguments. All groups are actual
group schemes over a field in arbitrary universe `u`.

`isUnipotent_of_kernel_of_quotient_of_fpqc` proves the existing all-test
fixed-vector unipotence predicate for an fpqc extension whose actual kernel and
quotient are unipotent. It follows the published finite-dimensional fixed-space
proof, replacing the two global affine models with
`normal_fixed_coordinates_of_affine_tests`. The nonzero kernel-fixed space has
split finite coordinates. The resulting representation kills the full kernel,
so the published fpqc homomorphism descent constructs an actual quotient
representation. A nonzero quotient-fixed vector gives a nonzero source-fixed
vector under the injective coordinate inclusion.

`SmoothUnipotentQuotient.range_le_comap_radical` treats a smooth connected normal
unipotent subgroup of an arbitrary source group mapping by a smooth, surjective,
quasi-compact homomorphism to an affine locally finite-type target with a
supplied radical. Smooth connected field groups are quasi-compact by
`quasiCompact_of_smooth_connected`. The actual schematic-image factorization
`QuasiCompactHomImage.ofSmoothConnected` therefore applies. The image is smooth,
connected and unipotent; fpqc square normality makes it normal in the target.
Target greatestness gives the asserted all-test image containment.

`isUnipotentRadical_preimage` additionally assumes the actual kernel is smooth,
connected and unipotent. Its finite type implies geometric connectedness.
The actual subgroup pullback is closed, smooth, connected and normal by the
published preimage geometry, and unipotent by the generalized extension theorem.
The preceding image argument establishes its full greatestness clause.
No radical-existence theorem for a nonaffine source is assumed.

`radical_comap_eq` compares this preimage radical with any supplied source
radical. `radicalPreimageIso` is the actual group-scheme isomorphism from that
source representative to the pullback representative; `radicalPreimageIso_hom_comp`
proves compatibility with their actual inclusions. The target remains affine
and locally of finite type, and the quotient projection remains smooth,
surjective and quasi-compact. This module does not assert existence of such a
quotient or prove its preservation under extension of the base field.
