# Zeroth homology of the actual right-derived unit

This module constructs the ordinary-value comparisons for an additive functor
applied to a degree-zero singleton, and proves that zeroth homology of its actual
bounded-below derived unit is the canonical map to its zeroth right-derived
functor.

The namespace is `Langlands.Cohomology.DerivedPlus`.

## Parameters and provenance

Let `C` and `D` be abelian categories, let `F : C ⥤ D` be additive, and suppose
`C` has enough injectives. For the localized constructions choose actual derived
categories of `C` and `D` in independent morphism universes `w` and `w'`.
The object and ordinary morphism universes of the two categories are independent
as well. The ordinary singleton, cycles and homology constructions do not
require derived-category choices or enough injectives.

This is an internal categorical construction for the cohomology framework. It
does not translate a new Harris or Berkovich passage. It uses the published
`DerivedPlus`, `DerivedPlusNaturality`, `DerivedPlusSource` and
`DerivedExactComposition` constructions, and the original implementations in the
pinned Mathlib files:

- `Algebra/Homology/SingleHomology.lean` and
  `Algebra/Homology/ShortComplex/HomologicalComplex.lean` for singleton terms,
  cycles and the zero-differential homology comparisons;
- `CategoryTheory/Abelian/Injective/Extend.lean` for the actual augmentation of
  the integer-indexed injective resolution and its degree-zero formula;
- `Algebra/Homology/Embedding/ExtendHomology.lean` for cycles and homology of an
  extended complex;
- `CategoryTheory/Abelian/RightDerived.lean` for the actual map
  `Functor.toRightDerivedZero` and its formula with any injective resolution.

No comparison, augmentation formula or desired homology equality is supplied
as an input.

## Singleton comparisons

`singlePlus X` is the actual complex with `X` in degree zero and zero elsewhere,
regarded as a bounded-below complex. This is the shared definition also used by
[`CohomologyPullbackDegreeZeroProof`](../AlgebraicGeometry/Modules/CohomologyPullbackDegreeZeroProof.md);
its type and body are unchanged from that module’s original definition.

`singleImageCyclesIso F X` identifies the degree-zero cycles of the termwise
image of this singleton with `F.obj X`. It first uses the vanishing outgoing
differential to identify cycles with the zero term, then applies `F` to the
canonical singleton-term isomorphism.

`singleImageHomologyIso F X` identifies its zeroth homology with `F.obj X`.
The incoming differential also vanishes, so the cycles-to-homology map is an
isomorphism; the definition composes its inverse with the cycles comparison.
The lemmas `singleImageCyclesIso_inv_iCycles` and
`singleImageCyclesIso_inv_homologyπ` record the corresponding inverse
factorizations.

`localizedSingleImageHomologyIso F X` first identifies homology after actual
localization with homology of this image complex, then uses the preceding
ordinary comparison. Its direction is

```text
H^0(Q_D(F(singlePlus X))) ≅ F(X).
```

## Augmentations and their homology

For any `I : InjectiveResolution X`, `singleIsoOfResolution_hom_eq_localized_augmentation` identifies
the published singleton-to-resolution isomorphism with localization of the
actual augmentation `I.ι'`. Its proof applies the fully faithful inclusion to
the unbounded derived category and simplifies the existing localization
comparison.

`singleUnit_comp_derivedComplexIso` applies naturality of the actual
right-derived unit at that augmentation. It says that the unit on the singleton
followed by the published derived-complex representative comparison equals
localization of `F` applied to the augmentation.

`singleToImageResolution F I` is this termwise augmentation followed by the
comparison between applying `F` after extension by zero and extending the image
resolution. Its target is the existing `imageResolution F I`.

`singleToImageResolution_cycles` proves that its map on degree-zero cycles,
through the singleton and extension comparisons, is precisely
`I.toRightDerivedZero' F`. The proof cancels the monic inclusion of cycles,
uses naturality of that inclusion and the extension cycles formula, and
substitutes the actual degree-zero augmentation formula. The remaining
calculation uses the published `map_extendXIso_hom` and cancels isomorphisms.
The full-subcategory comparison is exposed using the inclusion's fully
faithful preimage equation.

`singleToImageResolution_homology` then composes with the cycles-to-homology
map. Naturality of that map and its compatibility with extension reduce the
result to the preceding cycles calculation.

## The derived unit in degree zero

`rightDerivedFunctorPlusUnit_homology_zero` proves, for every `X : C`,

```text
H^0(F.rightDerivedFunctorPlusUnit at singlePlus X)
  followed by homologyNatIso(F, 0) at X
= localizedSingleImageHomologyIso(F, X).hom
  followed by F.toRightDerivedZero at X.
```

The proof chooses an injective resolution only to calculate the already
constructed maps. It expresses the natural homology comparison through that
resolution, combines the derived unit with its representative comparison, and
uses naturality of homology under localization. The preceding augmentation
homology equation and Mathlib's formula for `toRightDerivedZero` finish the
calculation. The statement is independent of the chosen resolution.

Only additivity is required of `F`. The theorem does not assert that the
canonical map to `R^0F` is invertible; that needs additional hypotheses such as
left exactness. No preservation of injectives or exactness by `F` is assumed.
Geometric degree-zero pullback comparisons and the remaining Harris
specializations are separate applications.
