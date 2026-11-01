# Localization of exact images of injective resolutions

This is internal categorical infrastructure for comparing an exact derived
source functor with the existing construction by mapped injective resolutions.
It uses actual Mathlib abelian categories, complexes, injective resolutions and
derived localizations. No desired augmentation or localization compatibility
is supplied as an input.

Let `C : Type uC` and `D : Type uD` be abelian categories with morphisms in
universes `vC` and `vD`. Let `T : C ⥤ D` be additive, preserve finite limits
and finite colimits, and preserve injective objects. Exactness supplies the
homology preservation used by `DerivedComparison.mapInjectiveResolution`.
Fix an actual injective resolution `I` of an object `X : C`. These constructions
need no assumption that every object of either category has a resolution.

`mappedResolutionComplexIso T I` is an isomorphism of bounded-below integer
cochain complexes

```text
T.mapCochainComplexPlus (resolutionPlus I)
  ≅ resolutionPlus (mapInjectiveResolution T I).
```

It specializes the existing `imageResolutionComparison T I`, which lifts the
inverse of the extension-by-zero comparison `mapExtendIso` through the fully
faithful inclusion of bounded-below complexes.
`mappedResolutionComplexIso_hom` identifies its underlying complex map with
that inverse. In every natural degree both complexes have the term obtained by
applying `T` to the corresponding term of `I`; in negative degrees the
comparison identifies their actual zero objects.

`mappedResolutionComplexIso_augmentation` proves the equality of complex maps

```text
singleComparison.inv at X
  ≫ T.mapHomologicalComplex.map I.ι'
  ≫ mappedResolutionComplexIso.hom.hom
  = (mapInjectiveResolution T I).ι'.
```

Here `singleComparison` is Mathlib's
`T.mapCochainComplexSingleFunctor 0`, and `I.ι'` is the actual augmentation of
the natural-indexed resolution extended by zero to integer degrees. The proof
reduces equality of maps from a singleton to degree zero. After postcomposing
with the target extension isomorphism, `map_extendXIso_hom` identifies the
term of the extension comparison. The augmentation formula and cancellation
of the singleton and extension isomorphisms finish the equation.

For the remaining constructions choose `HasDerivedCategory.{wC} C` and
`HasDerivedCategory.{wD} D`, with independent morphism universes `wC` and `wD`.
`localizedMappedResolutionIso T I` is the actual isomorphism

```text
T.mapDerivedCategory (DerivedCategory.Q I.cochainComplex)
  ≅ DerivedCategory.Q (mapInjectiveResolution T I).cochainComplex.
```

It composes `T.mapDerivedCategoryFactors` at the extended resolution with
localization of the inverse of `mapExtendIso`.
`localizedMappedResolutionIso_augmentation` proves

```text
(T.mapDerivedCategorySingleFunctor 0).inv at X
  ≫ T.mapDerivedCategory.map (DerivedCategory.Q.map I.ι')
  ≫ localizedMappedResolutionIso.hom
  = DerivedCategory.Q.map (mapInjectiveResolution T I).ι'.
```

Naturality of the localization factor moves the original augmentation past
that factor. Mathlib's singleton/factor compatibility then rewrites the initial
composite as localization of the ordinary singleton comparison. Functoriality
reduces the result to the proved complex augmentation equation.

The provenance is internal: this group compares existing constructions from
`DerivedPlus`, `DerivedComparison`, and `DerivedExactComposition` with Mathlib's
`DerivedCategory.ExactFunctor` constructions. It adds no new external theorem
or claim about a particular geometric site. Geometric specialization,
comparison of global-section maps, compact supports, equivariant actions and
Harris's specialized cohomology remain separate obligations.
