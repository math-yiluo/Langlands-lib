# Conditional radical images for incident unramified facets

This is an internal derived construction from the Library's facet filtration
comparisons and Henselian special-fibre image lifting. The full upstairs
radical-generation bound remains an explicit premise. No original-literature
theorem or unconditional radical-generation assertion is made here.

For general KP apartment data satisfying AS4,
`rootFixerPlus_eq_of_nonempty_subset_facet` identifies the positive root fixer
on any nonempty subset of a facet with the positive root fixer of the entire
facet. It uses a point of the subset, facet constancy of the positive
filtration, and antitonicity of the positive fixer.
`rootFixerPlus_le_rootFixer_of_incidentFacets_of_subsets` then compares
a nonempty subset of the face with any subset of the incident facet. Positive
fixers increase from face to facet, lie in the corresponding zero fixer, and
the zero fixer of the whole facet lies in that of its subset. No boundedness,
chamber hypothesis or choice of positive roots is needed.

Now let F be any nonarchimedean local field in universe u, K its actual
inertia fixed field, and O its fixed-field integer ring. Supply building
datum C for an arbitrary affine K-group G and any zero datum E. Let Ω be
nonempty and contained in a face Fa of a facet Ca, and let Ω' be any subset
of Ca. A subgroup H of G(K) is assumed to lie in E's zero subgroup and to
fix the entire apartment pointwise. H is not required to be a torus in
this helper: only the stated subgroup bound is used.

`unramifiedIncidentGeneratedGroup_le_zeroFixer` proves that H joined with
all positive root fixers on Ω lies in the zero fixer of Ω'. The bound
for H restricts its full-apartment action. Each positive root piece lies
in the corresponding zero root fixer of Ω' by the preceding comparison;
`rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer` puts that zero root
fixer in E's zero subgroup intersected with the pointwise fixer of Ω'.

Let N and N' be actual integral models of G over O, with the integral
points of N' equal to that zero fixer of Ω'. For any morphism
`i : U ⟶ N.specialFibre`, retain the explicit premise that the generic
image of the **entire** reduction preimage of the rational-point image
of i lies in H joined with all positive root fixers on Ω.
`unramifiedIncidentReductionPreimage_le_integralPoints` composes this
premise with the preceding bound to put that whole group in N'.integralPoints.
No characterization or smoothness of N is used for this subgroup step.

Finally suppose N is smooth, `ψ : N'.Hom N (𝟙 G)` is an actual model
homomorphism, and i represents the full unipotent radical of N's special
fibre. `unramifiedIncidentRadicalImageFactor` constructs a morphism from
U into the actual schematic image of ψ's special-fibre map. The companion
composition theorem identifies its composite with the actual closed image
inclusion with i. `unramifiedIncidentRadical_range_le_image` gives the
resulting subgroup-functor containment on every residue-scheme test.

These constructions apply `specialFibreImageFactorOfPreimage` and its
compatibility theorem to the derived generic containment. The fixed-field
integer ring is Henselian and its residue field is algebraically closed by
the proved separable-unramified arithmetic. The radical's smoothness gives
local finite type and reducedness over the residue field, using
`isReduced_of_smooth_over_field`. Smoothness of N' is not required.
Neither nonemptiness of Ω' nor boundedness of either set is required.

The retained generation upper bound is the precise missing mathematical
input. A full upstairs root-generation equality implies it, but this module
does not prove that equality or import its unreviewed statement. It does
not prove parabolicity, descent of the image, rational surjectivity of the
image projection, the reduction-preimage equality, or the host facet theorem.
