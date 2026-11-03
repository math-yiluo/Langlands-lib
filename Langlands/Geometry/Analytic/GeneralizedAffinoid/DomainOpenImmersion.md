# Open full affinoid domains as actual open immersions

Author: Worker 36.

Let `K` be a complete ultrametric normed field, `A` an actual presented
positive-polyradius affinoid algebra, and `d : Domain K A` a full represented
affinoid domain. If `d.locus` is open, the previously constructed morphisms of
algebra-sheafed spaces, ring-sheafed spaces and locally ringed spaces induced by
`d.baseMap` are open immersions. The intrinsic structured spaces are isomorphic
to the ambient restrictions along this actual structural open embedding.
Each comparison factors the original bounded-map morphism.

The extra openness assumption is explicit. The represented locus of a full
affinoid domain is already closed and compact, so this hypothesis applies here
to open full affinoid domains. It does not cover arbitrary ordinary open
subspaces by itself.

## Invertibility on contained ambient opens

`openAlgebraPresheafMap_app_isIso d U hU` applies to every ambient ordinary open
`U` with `hU : U ⊆ d.locus`, even when the whole domain locus is not open. It
proves that the component of `RationalChart.openAlgebraPresheafMap d.baseMap`
at `U` is an isomorphism in `CommAlgCat K`. This is the actual component

```text
CommAlgCat.ofHom (OpenSections.pullback d.baseMap U).
```

The proof rewrites it as the forward homomorphism of
`CommAlgCat.isoMk (d.openSectionsEquiv U hU)`. The needed map equality is
`openSectionsEquiv_toAlgHom` from `DomainOpenPullbackComparison`. Thus the
component is the original bounded-map pullback on compatible families of
actual rational quotient elements.

`openRingPresheafMap_app_isIso` proves the corresponding assertion for the
component of the existing `ringSheafedSpaceMap d.baseMap`. Its component is
definitionally the image of the algebra component under
`forget₂ (CommAlgCat K) CommRingCat`; functors preserve isomorphisms.

## The actual morphisms are open immersions

For `hd : IsOpen d.locus`, `spectrumMap_isOpenEmbedding` proves that
`RationalChart.openSpectrumMap d.baseMap` is an open embedding. Its embedding
part is the published `Domain.spectrumEmbedding` theorem, and its open-range
part is `hd` transported along the represented exact-image identity
`Set.range d.spectrumMap = d.locus`. No spectral injectivity or topology is
assumed as additional data.

`algebraSheafedSpaceMap_isOpenImmersion` proves Mathlib's
`SheafedSpace.IsOpenImmersion` predicate for the existing
`algebraSheafedSpaceMap d.baseMap`. This predicate requires that its base map
be an open embedding and that its presheaf components on images of intrinsic
opens be isomorphisms. The image of every intrinsic open is contained in
`d.locus`, by `d.represents.hasImageIn`. The preceding component result supplies
exactly these isomorphisms.

`ringSheafedSpaceMap_isOpenImmersion` uses the same open embedding and the
scalar-forgotten component result. Finally,
`locallyRingedSpaceMap_isOpenImmersion` applies to the already constructed
`RationalChart.locallyRingedSpaceMap d.baseMap`: its underlying
presheafed-space morphism is definitionally the same ring-sheaf morphism. The
original morphism's locality proof on genuine ordinary-open stalks, from
`RationalOpenMorphism`, is retained.

## Restriction comparisons over the ambient spaces

`algebraSheafedSpaceRestrictIso`, `ringSheafedSpaceRestrictIso` and
`locallyRingedSpaceRestrictIso` construct the respective isomorphisms

```text
intrinsicSpace K d.algebra ≅
  (ambientSpace K A).restrict (d.spectrumMap_isOpenEmbedding hd).
```

Here `restrict` is Mathlib's restriction along an open embedding. Its carrier
is `BanachSpectrum d.algebra`; on an intrinsic open `V` its presheaf value is
the original ambient presheaf on the image of `V` under the structural map.
This is an ambient restriction along the actual spectral embedding, whose
range is the represented locus.

The algebra and ring comparisons use
`SheafedSpace.IsOpenImmersion.isoRestrict` with the proved open-immersion
predicates. The locally ringed-space comparison uses
`LocallyRingedSpace.IsOpenImmersion.isoRestrict`, which lifts the underlying
sheafed-space isomorphism using the locality of isomorphisms on genuine
stalks. Mathlib's construction forms a natural isomorphism from the existing
components on image opens, followed by presheaf transport along the equality
between an intrinsic open and the preimage of its image. That equality follows
from injectivity of the base embedding. Thus the comparison retains the
actual sheaf components and their naturality.

`algebraSheafedSpaceRestrictIso_hom_base` and
`locallyRingedSpaceRestrictIso_hom_base` expose the identity base map of the
comparisons. Each `...RestrictIso_hom_ofRestrict` theorem proves

```text
comparison.hom ≫ ambientSpace.ofRestrict embedding =
  originalBoundedMapMorphism.
```

These equations are the corresponding Mathlib `isoRestrict_hom_ofRestrict`
laws applied to the constructed original morphisms. They identify the
comparisons over the original ambient structured spaces.

`openStalkMap_isIso` and `openRingStalkMap_isIso` additionally prove
invertibility of the original `RationalChart.openStalkMap d.baseMap y` and
`openRingStalkMap d.baseMap y` for every intrinsic point `y`. They use Mathlib's
stalk-isomorphism theorem for open immersions. Their maps are the genuine
stalk-colimit maps already constructed in `RationalOpenMorphism`.

## Provenance and scope

This is an internal derivation from `DomainOpenPullbackComparison`,
`RationalOpenMorphism`, the full-domain spectral embedding imported through the
former module, and Mathlib's `Geometry.RingedSpace.OpenImmersion` APIs. It
supplies their hypotheses for the actual constructed geometry and reuses their
restriction and stalk constructions. No additional original-literature
assertion or assumed analytic output is introduced.

The coefficient field may have trivial valuation, and the presented algebras
may be nonreduced or zero, with arbitrary positive polyradii. Empty domains,
spectra and opens are allowed. The section maps retain actual quotient
elements, including nilpotents. The bundled restriction and stalk comparisons
require the displayed openness hypothesis. No ordinary inverse-image sheaf
comparison for a closed non-open domain follows from this module.

Unrestricted analytic atlases, analytic etale and quasi-etale morphisms and
sites, their equivariant versions, distinguished domains and the Harris tower
remain separate construction obligations.
