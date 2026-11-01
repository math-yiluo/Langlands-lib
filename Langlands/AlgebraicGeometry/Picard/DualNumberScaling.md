# Actual epsilon scaling on a scheme thickening

Let `k : Type u` be an arbitrary field, `X : Scheme.{u}`, and
`f : X ⟶ Spec k`. For every `c : k`, including zero, `scale f c` is the
actual endomorphism of `thickening f` obtained by base-changing the test-scheme
endomorphism `Spec.map (epsilonScale c)`. It is constructed with
`pullback.map`, the identity on `X` and the identity on `Spec k`.

`scale_projection` and `scale_structure` identify its composites with both
actual projections. The first is the unchanged projection to `X`; the
second is the actual structure map followed by the test-scheme scaling.
`closedPoint_scale` proves that this morphism fixes the actual zero section.
This uses the first-coordinate identity for `epsilonScale` and the
universal property of the genuine scheme pullback. No inverse for `c` is used.

## Actual sections

For every open `U` of `X`, `scaleSectionMap f c U` is the actual ring map
induced by `scale f c` on sections over `projection f ⁻¹ᵁ U`. The equality
of the composite scaling and projection with the projection proves that
this inverse-image open maps to itself.

`projection_scaleSectionMap` shows that this ring map fixes every section
pulled back along the first projection. `testSectionMap_scaleSectionMap`
shows that the constant dual-number section map intertwines it with
`epsilonScale c` on `DualNumber k`.

`baseSectionMap_comp_app` proves the naturality of the normalized base-field
section map under any scheme morphism. Applied to the actual pullback
square, together with naturality of `Scheme.ΓSpecIso`, it gives
`baseSectionMap_projection`. In particular `testSectionMap_constant`
identifies a constant field section from the test scheme with the first
projection of the corresponding base-field section on `U`.

Applying the test-section identity to epsilon and using this constant
identity proves

```
scaleSectionMap f c U (epsilonSection f U)
  = projection.app U (baseSectionMap f U c) * epsilonSection f U.
```

Thus actual scaling fixes coefficient sections and multiplies the actual
epsilon section by the specified field element, interpreted through the
actual base-field section map.

## Coordinates and units

`scaleSectionMap_sectionMap` proves equality of the ring homomorphisms

```
scaleSectionMap ∘ sectionMap
  = sectionMap ∘ epsilonScale (baseSectionMap f U c).
```

It applies the explicit formula for `sectionMap`, preservation of sums and
products, and the two previously proved projection/epsilon formulas.
`scaleSectionMap_sectionEquiv` gives the same compatibility for the
canonical equivalence of actual sections with dual numbers of original
sections.

For actual coefficient units, `scaleSectionMap_coefficientUnit` proves

```
Units.map (scaleSectionMap f c U) (coefficientUnit f U a)
  = coefficientUnit f U (baseSectionMap f U c * a).
```

The proof uses the explicit actual unit formula `1 + p*(a)*epsilon` and
the section formulas. All assertions hold over every open, with no
affineness, finiteness, separation or nonzero-scalar hypothesis.

## Provenance and scope

This is an internal geometric compatibility construction. It extends the
published affine scaling calculation in `DualNumberBaseChange` to an
arbitrary scheme using the actual pullback projections, and proves its
section and unit formulas from `DualNumberStructure`,
`DualNumberActualUnits` and `DualNumberCocycles`. It does not assume a
scalar compatibility statement about deformations or tangent spaces.

The result provides the actual scheme and section maps needed for later
scalar compatibility. This module does not yet identify pullbacks of
rigidified deformation classes with scaled cohomology classes or prove
the final tangent-to-H1 linear equivalence.
