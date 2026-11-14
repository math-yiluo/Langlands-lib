# Dynamic parabolics in actual neutral incident comparison images

This internal derived unit combines the actual neutral centralizer and positive
dynamic image containments. It works at arbitrary universe `u` and retains full
unipotent radical containment as an explicit premise for parabolic recognition.

Let `F` be a nonarchimedean local field, `K` its inertia fixed field, and `O` the
fixed-field integer ring. Supply maximal-unramified building data `C` for an
affine `K`-group `G`, together with two actual relative-component model packages
`M` and `M'`. Their full models have integral points equal to the character
valuation kernel intersected with the pointwise fixers of the apartment images
of `Ω` and `Ω'`, respectively. Supply a generic-identity neutral comparison
`ψ : M'.neutral.Hom M.neutral (𝟙 G)`. The nonempty subsets `Ω` and `Ω'` lie in a
face `Fa` and its incident facet `Ca`, respectively.

The integral split torus is `unramifiedNeutralSplitTorusData C M Ω hM` in the
actual target neutral model. The cocharacter is the canonical specialization
of `C.incidentFacetCocharacter hCa hFaCa`. The first theorem,
`unramifiedNeutralIncidentCocharacter_specialization_isGeneric`, proves that it
is generic for the adjoint roots of the full target neutral special fibre.
It uses genericity of the building cocharacter and the preserved and reflected
genericity of integral-torus specialization. This theorem only uses the target
full-model point formula and the facet incidence; it does not need the source,
comparison, subset nonemptiness, or subset containments.

`unramifiedNeutralIncidentCocharacter_centralizer_eq_torusCentralizer` identifies
the dynamic centralizer of this specialized cocharacter with the entire actual
residue-torus centralizer on every scheme test. Smoothness and connectedness of
the target neutral fibre follow from `M.neutral_smooth` and
`M.neutral_connectedFibres`; they are not additional caller premises.

`unramifiedNeutralIncidentDynamicParabolic_le_image` proves containment of the
entire dynamic parabolic in the schematic image of the actual neutral
special-fibre comparison. The image and the dynamic subgroup are both taken
in the full target neutral residue fibre. The proof combines
`unramifiedNeutral_specialCentralizer_le_image` and
`unramifiedNeutralIncidentDynamicUnipotent_le_image` using genericity and the
centralizer/unipotent factorization of a dynamic parabolic. The fibre can be
nonreductive.

`unramifiedNeutralIncidentDynamicParabolicImagePoints` packages this containment
as a group homomorphism on each residue-scheme test. It is subgroup inclusion,
and `unramifiedNeutralIncidentDynamicParabolicImagePoints_val` proves that it
preserves the underlying ambient point.

For `unramifiedNeutralIncidentImage_isParabolic_of_radical_le`, supply an actual
representative `r : U ⟶ M.neutral.specialFibre` of the full unipotent radical and
assume its whole subgroup-functor range lies in the comparison image. Smoothness
of the source neutral fibre gives geometric reducedness, so the schematic image
is smooth by `HomImage.smooth_image`; its inclusion is closed. The residue field
is algebraically closed by `fixedFieldResidueIsAlgClosure`. Full-radical
parabolic recognition then applies using the preceding dynamic containment.

The provenance is composition of the imported genericity, actual neutral image,
connected-fibre, and radical-recognition interfaces. No global identification of
neutral integral points with a supplied zero subgroup is assumed. This unit does
not establish full radical containment, congruence containment, exact reduction
preimages, model existence, or the unconditional depth-zero opposite-factor
statement.
