# Recovering integral-point order from special-fibre images

This internal derived module works at arbitrary universe `u` with the actual
integral models, generic-point maps, reductions and schematic images in the
Library. Its provenance is composition of generic-point injectivity, smooth
connected affine image theory, algebraically closed point lifting, the
reduction-preimage criterion, and detection of closed subgroup containment by
rational points of a reduced scheme. It translates no additional external
literature claim.

All declarations are in
`Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom`. Fix a
commutative domain `R`, a fraction field `K`, a group scheme `G/K`, and
`φ : RelativeComponentModelHom source target`. Both relative-component model
pairs carry affine models of finite type, smooth full and neutral models, and
connected neutral fibres. The homomorphism has the identity as generic map.
No building, facet, reductivity or parabolicity assumption is used.

For these data, without a local-ring assumption:

- `sectionRange_eq_comap_integralPoints` identifies the image of the neutral
  integral-section homomorphism with the inverse image of the source's generic
  integral-point subgroup under the target's generic-point map. Naturality
  proves one inclusion, and injectivity of the target generic-point map gives
  the other.
- `neutralSectionMap_injective` follows from the same naturality and
  injectivity of the source generic-point map.
- `sectionRange_le_iff_integralPoints_le` compares another morphism
  `ψ : RelativeComponentModelHom source₂ target`. It proves that inclusion of
  the two neutral section images in the common target is equivalent to
  inclusion of the source generic integral-point subgroups. The previous
  inverse-image identity and the fact that the first source's generic points
  lie in the target range prove this equivalence.

`specialFibreImageProjection_surjective_of_isAlgClosed` assumes the residue field is
algebraically closed and `R` is local. Base change gives smooth affine neutral
special fibres of finite type; connected neutral fibres imply connectedness of
the actual neutral special fibre. The source special fibre is therefore
geometrically integral by `smoothConnectedAffineGeometry`. Its canonical
projection to the actual schematic image is surjective by
`HomImage.surjective_projection`, and locally of finite type by the image
theory instance. `GroupScheme.rationalPoints_surjective` then lifts every
rational point over the original residue field.

The remaining results assume `R` is Henselian and its residue field is
algebraically closed. They retain the explicit generic congruence containment
`target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints`.

`hasParabolicReductionPreimage_of_congruence` proves the unchanged
`φ.HasParabolicReductionPreimage` predicate. It supplies the just-proved
rational surjectivity and the carried source smoothness to
`hasParabolicReductionPreimage_iff`, and converts the generic congruence
containment using `congruenceKernel_le_sectionRange_iff`. Thus the full
reduction preimage of `φ.specialFibreImagePoints` equals the neutral section
image.

`reductionPreimageMulEquiv` constructs a multiplicative equivalence from
`source.neutral.integralSections` onto that full reduction-preimage subgroup
of `target.neutral.integralSections`. It composes `MonoidHom.ofInjective`
for the neutral section map with `MulEquiv.subgroupCongr` for the established
preimage equality. `reductionPreimageMulEquiv_apply` states, definitionally,
that its underlying section is the original neutral section map. In
particular this is a group equivalence with a proved forward specification.

For a second morphism `ψ` to the same target, assume also
`target.neutral.congruenceSubgroup ≤ source₂.neutral.integralPoints`.
`specialFibreImagePoints_le_iff_integralPoints_le` proves
`φ.specialFibreImagePoints ≤ ψ.specialFibreImagePoints` if and only if
`source.neutral.integralPoints ≤ source₂.neutral.integralPoints`. Smooth
Henselian reduction for the target reflects subgroup order through inverse
images; the two exact reduction-preimage identities reduce the assertion to
the earlier section-image comparison.

`specialFibreImage_le_iff_integralPoints_le` upgrades this comparison to
containment of `SubgroupFunctor.range φ.specialFibreImageInclusion` in
`SubgroupFunctor.range ψ.specialFibreImageInclusion` on every residue-scheme
test. Smoothness of the source fibre implies geometric reducedness, and
`HomImage.smooth_image` gives a smooth, hence reduced, schematic image of
finite type. The second image inclusion is a closed subgroup. The published
`SubgroupFunctor.range_le_iff_algClosed_points` therefore identifies all-test
containment with the rational-point containment just proved.
`specialFibreImage_eq_iff_integralPoints_eq` applies both directions of this
order comparison and antisymmetry to obtain the corresponding equality
criterion.

The subgroup functors in these final results are the closed inclusions of the
actual schematic images, rather than the possibly smaller all-test ranges
of the original special-fibre morphisms. Rational lifting was proved using
the algebraically closed residue field; no smoothness or unipotence premise
on the special-fibre kernel is needed. Congruence containment remains an
explicit hypothesis for each source. The results assert neither facet-specific
congruence containment, parabolicity, a classification of images, nor the host
`UnramifiedFacetParabolicOrderStatement`.
