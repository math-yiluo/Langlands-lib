# Named canonical derived Čech comparison

Author: Worker 606.

This internal extension of `CechResolution.Comparison` names the canonical
map implicit in `nonempty_cechCochainComplex_iso`. For a ring object `R`,
a scheme morphism `f : X ⟶ Spec R`, an ordered affine cover `𝒰`, and an
actual module sheaf `M`, all in arbitrary common universe `u`,
`cechDerivedComparison f 𝒰 M` maps the image in the derived category of
the alternating Čech cochain complex (extended by zero to integer degrees)
to the actual right derived complex of relative global sections at `M`.
Its definition requires neither separatedness nor quasi-coherence.

`cechSectionsDerivedComparison` is the intermediate map whose source is
the extension of relative global sections of the sheafified Čech complex.
It first applies the inverse of `extendMapIso` to commute applying sections
with extension, then applies `derivedResolutionComparison` to the actual
Čech augmentation. The augmentation is a quasi-isomorphism by the published
`quasiIso_cechAug`. The named alternating-cochain map first applies `Q` to
the extension of `sectionsComplexIso.inv`, then this intermediate map.
Thus these maps use the augmentation and the canonical resolution comparison,
not a choice from the nonempty isomorphism theorem.

For separated `f` and quasi-coherent `M`,
`isIso_cechSectionsDerivedComparison` applies the published
`isIso_derivedResolutionComparison`, with every positive-degree term
vanishing supplied by `isZero_relativeCohomology_cechTerm`.
`isIso_cechDerivedComparison` additionally uses the sections-complex
isomorphism. `cechDerivedComparisonIso` is `asIso` of this exact named map;
`cechDerivedComparisonIso_hom` states that its forward map is definitionally
`cechDerivedComparison`.

The provenance is internal: the module exposes the concrete composite already
used in the published comparison proof and proves invertibility from the
same imported acyclicity theorem. It does not assert a base-change square,
arbitrary derived scalar base change, a perfect representative, or the
relative cube theorem.
