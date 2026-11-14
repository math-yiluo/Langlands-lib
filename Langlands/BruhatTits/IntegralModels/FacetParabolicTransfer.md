# Actual special-fibre images through the reductive quotient

This internal construction specializes the published unipotent-quotient
parabolic order isomorphism to supplied reductive quotients of the actual
neutral special fibres. It does not construct the facet-to-parabolic
geometric bijection.

The imported
`SpecialFibreQuotientData.hasSmoothConnectedUnipotentKernel` from
`ReductiveQuotientExistence` identifies the actual kernel using the specified
smooth, connected, unipotent radical and the fppf quotient's exactness.
The neutral special fibre is affine and smooth by base change; its
connectedness follows from connected fibres of the neutral integral model.
The published `UnipotentQuotientParabolics.parabolicComapOrderIso` therefore
applies.

For a model morphism whose actual special-fibre image is parabolic, the
published quotient correspondence constructs a parabolic closed image
with the exact full inverse-image equality. Its projection is surjective.
The image is smooth over the residue field, hence reduced, so that this
projection is schematically dominant. Composing it with the original
schematic-image projection gives a dominant factorization of the same
map that defines the actual reductive image. Equality of the ranges of
closed dominant factorizations identifies the constructed parabolic
with that actual image and transfers the full inverse-image equality.

`HasFacetSpecialFibreParabolicBijection` records the remaining geometric
input as bijectivity of the actual special-fibre image map onto all
parabolic subgroup functors. Given that input, each actual quotient image
is parabolic by the comparison just proved. Equality of two quotient
images gives equality of their full inverse images, so the input
bijection proves injectivity. For a parabolic of the quotient, its full
inverse image is a parabolic of the neutral special fibre; the input
bijection realizes it by a facet. Injectivity of the quotient parabolic
order isomorphism then identifies that facet's actual quotient image
with the prescribed parabolic. The unconditional incidence lemma supplies
the opposite-inclusion clause of the existing
`HasFacetParabolicOrderBijection`.

All results are derived from the published schematic-image, connected
special-fibre, smooth reducedness, and unipotent quotient APIs. The new
predicate is an internal intermediate input. No claim is made here that
the building or model-characterization hypotheses imply that input, and
the existing target statement and its import closure are unchanged.
