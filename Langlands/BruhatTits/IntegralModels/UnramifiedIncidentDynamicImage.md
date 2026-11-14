# Dynamic positive subgroups in incident special-fibre images

This internal supporting construction proves containment of the actual dynamic
positive subgroup in the schematic image of a comparison between incident
unramified zero-fixer models. All subgroup containments are on every residue
scheme test. The full target special fibre may be nonreductive or disconnected.

The general theorem
`RelativeRoot.dynamicUnipotent_le_of_positive_rootSubgroups_le` works in a smooth
affine group over a field with a split torus map. It assumes disjoint rays for
indivisible positive roots and containment of the positive root functors in a
subgroup functor. It realizes the positive weight semigroup by a smooth connected
unipotent group, partitions its weight support by those rays, and applies the
published ordered semigroup product theorem inside that unipotent group. The
cyclic root comparison identifies every factor with its actual root functor.
On each test scheme the ordered multiplication isomorphism writes each dynamic
unipotent point as a product of points of these factors; subgroup closure gives
the asserted containment.

For a smooth integral model with compatible integral split torus,
`IntegralSplitTorusData.mem_indivisibleRoots_characterSpecialization_iff` shows
that the canonical generic-to-residue character equivalence preserves
indivisibility in the full root set. Its proof transports root membership,
natural-number multiplication, and the divisibility witnesses in both
directions. Consequently
`disjoint_cyclicTail_special_indivisiblePositiveRoots` transports the generic
root system's disjoint indivisible rays to the full special fibre.

The main theorem `unramifiedIncidentDynamicUnipotent_le_image` uses the actual
integral torus supplied by `unramifiedZeroFixerIntegralSplitTorusData`. Its
cocharacter is the canonical specialization of `C.incidentFacetCocharacter`
for a face `Fa` of a facet `Ca`. The target and source models have integral
points equal to the intersections of the zero subgroup with the pointwise
fixers of nonempty subsets `Omega` of `Fa` and `Omega'` of `Ca`, respectively.
The target model is smooth, and the supplied model morphism has generic map
the identity. Canonical character specialization and its pairing identity
carry each positive special-fibre root to a positive generic root. The published
`unramifiedIncidentPositiveRoot_range_le_image` and actual residue root
representability then give the positive-root containment needed by the general
theorem. No additional sign or root-support premises are supplied by the caller.

The construction `unramifiedIncidentDynamicUnipotentImagePoints` is the
resulting canonical group homomorphism from dynamic positive points to incident
image points on each residue-scheme test. Its value formula proves that the
underlying ambient point is unchanged. It is the pointwise inclusion supplied
by the containment theorem.

The construction is derived from the cited Lean interfaces, including the
ordered semigroup product and root-ray decompositions, the generic relative
root system, and the actual incident root-image theorem. It asserts dynamic
unipotent containment only. It supplies neither containment of the full
unipotent radical nor parabolic recognition or a facet-order bijection.
