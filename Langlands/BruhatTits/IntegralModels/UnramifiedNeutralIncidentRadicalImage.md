# Radical and congruence transfer for actual neutral incident models

This internal construction transfers an explicit generation bound to actual
neutral components of supplied full apartment-fixer models. It adapts
`UnramifiedIncidentRadicalImage` without a prescribed zero-fixer formula for
neutral integral points.

Let `C` be maximal-unramified building data for an affine group over the
inertia-fixed field of a nonarchimedean local field `F`, at arbitrary universe
`u`. Supply relative-component model packages `M` and `M'`. Their **full**
integral-point groups must be the character-valuation kernel intersected with
the pointwise fixers of `Ω` and `Ω'`, respectively. Assume `Ω` is nonempty and
contained in a facet `Fa` which is a face of the facet `Ca`, and `Ω' ⊆ Ca`.
No model or building existence is asserted.

`unramifiedNeutralPositiveRootCentralizerGroup` is the join of the image of the
entire actual target neutral-centralizer integral-point group and **all**
strict-depth root fixers `rootFixerPlus a Ω`. The centralizer here is the
closed centralizer inside `M.neutral`, supplied by
`unramifiedNeutralCentralizerModel`; it is not the centralizer of the possibly
disconnected full model. The group is an upper bound convenient for transfer,
not a claimed formula for the radical preimage.

`unramifiedNeutralIncidentGeneratedGroup_le_neutral` puts this whole join in
`M'.neutral.integralPoints`. For the centralizer factor, the published
`unramifiedNeutralCentralizerModel_integralPoints_le` compares the actual
neutral centralizers from a nonempty target subset, and their integral-model
maps land in the source neutral. For each root, the incident-facet
strict-depth comparison puts the target positive fixer in the source
depth-zero root fixer; the published actual-neutral root intersection formula
puts that fixer in the source neutral.

For any group morphism `i : U ⟶ M.neutral.specialFibre`, the remaining
generation premise `hgen` concerns the **entire** group

```text
((rationalPoints.map i).range.comap M.neutral.reduction).map
  M.neutral.integralPointMap
```

and bounds it by the join just defined. This is an assumption, not a proved
generation theorem. Transitivity gives
`unramifiedNeutralIncidentReductionPreimage_le_neutral`. The target congruence
kernel reduces to the identity, which lies in the rational-point range of
every group morphism. Mapping this kernel to generic points therefore gives
`unramifiedNeutralIncidentCongruence_le_neutral` from the same bound, with no
radical hypothesis on `i`.

When `i` represents the full unipotent radical, its smoothness makes its source
reduced and locally of finite type. The target neutral is smooth, the
fixed-field integer ring is Henselian, and its residue field is algebraically
closed. `IntegralModel.Hom.specialFibreImageFactorOfPreimage` then constructs
`unramifiedNeutralIncidentRadicalImageFactor` into the actual schematic image
of a supplied generic-identity neutral comparison `ψ`. Its composite with the
image inclusion is exactly `i`, so
`unramifiedNeutralIncidentRadical_range_le_image` holds on every residue-scheme
test. With `Ω'` additionally nonempty, the actual-neutral incident
dynamic-parabolic theorem gives geometric parabolicity of that image.

For a supplied full component-model comparison `φ : RelativeComponentModelHom
M' M`, the congruence containment gives its exact reduction-preimage property.
The existing `SpecialFibreImageRecovery` theorem supplies rational
surjectivity of the actual image projection from algebraic closedness and
smooth connected neutral fibres. The definition
`unramifiedNeutralIncidentReductionPreimageEquiv` is the resulting group
equivalence from the original source integral sections to the full target
reduction preimage of the actual image. Its value is precisely the supplied
neutral section map, as the final theorem states.

The provenance is composition of these existing interfaces and the elementary
identity-in-range argument. The construction proves neither the explicit
generation premise nor full-model existence or descent. In particular it does
not prove the unchanged host
`UnramifiedFixedDepthZeroOppositeStatement`.
