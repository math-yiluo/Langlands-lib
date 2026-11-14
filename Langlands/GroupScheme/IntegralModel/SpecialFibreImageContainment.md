# Special-fibre image containment from generic reduction preimages

This is an internal construction derived from smooth Henselian reduction,
generic injectivity of integral sections, naturality of model maps, the actual
schematic image, and detection of closed subgroup containment on algebraically
closed field points. It introduces no new external-source assertion.

Let `φ : M.Hom N (𝟙 G)` be an identity-generic-fibre map of affine flat
finite-type integral models over a Henselian local domain `R`, with fraction
field `K`. Let `i : U ⟶ N.specialFibre` be any homomorphism of group schemes
over the actual residue field of `R`. The map `i` need not be a closed immersion.

The common input is that the generic image of every integral section of `N`
whose reduction lies in the residue-field point image of `i` belongs to
`M.integralPoints`. Explicitly this is

```lean
((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap ≤
  M.integralPoints
```

`Hom.specialFibreImagePoints_contains_of_preimage` assumes that `N` is smooth.
It lifts a point in the rational image of `i` to an integral section of `N`
using `IntegralModel.reduction_surjective`. The input supplies an integral
section of `M` with the same generic point. Generic injectivity identifies its
image under `φ` with the original section of `N`. Reduction naturality and
`SchematicImage.projection_inclusion` then give a rational point in the actual
schematic-image group mapping to the starting point. Smoothness of `M` and
rational surjectivity of the schematic-image projection are not required.

When the residue field is algebraically closed and `U` is reduced and locally
of finite type, `Hom.specialFibreImage_contains_of_preimage` upgrades this to
containment of subgroup functors on every residue-scheme test. It uses
`SubgroupFunctor.range_le_of_algClosed_points`, whose target is closed because
it is the actual schematic-image inclusion.

Under those same hypotheses, `Hom.specialFibreImageFactorOfPreimage` constructs
a group-scheme homomorphism `U ⟶ SchematicImage.image φ.specialFibreMap`.
`Hom.specialFibreImageFactorOfPreimage_comp` proves that its composite with the
image inclusion is the original `i`.

For a supplied smooth unipotent radical, the displayed input is exactly
containment of the generic positive subgroup in the source integral-point
image. The construction does not prove that input from facet incidence, does
not identify radicals after base change, and does not assert parabolicity. In
an unramified application the containment must hold over the actual upstairs
integers; a containment restricted to original-field rational points does not
suffice for the all-test conclusion.
