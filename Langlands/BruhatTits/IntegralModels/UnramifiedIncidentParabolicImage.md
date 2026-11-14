# Conditional parabolicity of incident special-fibre images

This internal derived unit combines the actual incident cocharacter,
centralizer and positive dynamic image containments with full-radical
parabolic recognition. All objects have arbitrary universe `u`. No
unconditional radical-generation assertion is made.

Let F be a nonarchimedean local field, K its inertia fixed field, and O its
fixed-field integer ring. Supply maximal-unramified building data C for an
affine K-group G and a zero datum E. Let Fa be a face of a facet Ca.
The nonempty apartment subsets Ω and Ω' lie in Fa and Ca respectively.
The actual integral models N and N' have integral points equal to
E.zeroPoints intersected with the pointwise fixers of their respective
apartment subset images. The target N is smooth and its full special fibre
is connected. Supply an actual generic-identity model morphism
`ψ : N'.Hom N (𝟙 G)`.

`unramifiedIncidentDynamicParabolic_le_image` contains the full dynamic
parabolic of the canonical specialization of C's chosen incident
cocharacter in the actual schematic image of ψ's special-fibre map.
Both functors are taken in the full target special fibre and evaluated
on every residue-scheme test. The target fibre may be nonreductive.
The proof uses the actual zero-fixer integral split torus. Its canonical
cocharacter specialization is generic by
`unramifiedIncidentCocharacter_specialization_isGeneric`. The full residue
torus centralizer lies in the comparison image by
`unramifiedZeroFixer_specialCentralizer_le_image`, and the positive
dynamic subgroup lies there by `unramifiedIncidentDynamicUnipotent_le_image`.
The generic centralizer comparison and the dynamic centralizer/unipotent
factorization then contain the full dynamic parabolic.

`unramifiedIncidentDynamicParabolicImagePoints` is the resulting canonical
group homomorphism on each test scheme. It is subgroup inclusion, and its
value theorem shows that the underlying ambient point is unchanged.
Neither this construction nor the preceding containment needs smoothness
of N'.

For `unramifiedIncidentImage_isParabolic_of_radical_le`, also assume N'
is smooth and supply an actual representative `r : U ⟶ N.specialFibre`
of the full unipotent radical. Retain explicitly that the whole range
of r lies in the comparison image on every test. Smoothness of N'
gives geometric reducedness of its special fibre. `HomImage.smooth_image`
therefore makes the actual schematic image smooth; its inclusion is
closed. The residue field is algebraically closed by the proved
maximal-unramified arithmetic. The full-radical recognition theorem
applies to this smooth closed subgroup, using the preceding dynamic
parabolic containment and the supplied radical containment.

`unramifiedIncidentImage_isParabolic_of_rootGeneration` replaces that
all-test radical containment with the explicit upstairs bound

`((rationalPoints.map r).range.comap N.reduction).map N.integralPointMap
  ≤ H ⊔ ⨆ a : relativeRoots C.i, C.apartment.rootFixerPlus a Ω`.

Here H lies in E.zeroPoints and fixes the entire apartment pointwise.
The previously derived `unramifiedIncidentRadical_range_le_image` applies
the incident positive-root comparison and Henselian lifting to this
bound and supplies the required containment. The bound concerns the
entire radical preimage over O, including every residue-field radical
point, rather than a pullback to the original field F.

The provenance is composition of the imported Library interfaces and the
actual-model supporting results just named. This unit leaves that
upstairs generation bound unproved. It does not descend parabolicity to
F, prove the integral reduction-preimage equality, or prove
`UnramifiedFacetParabolicImageStatement`.
