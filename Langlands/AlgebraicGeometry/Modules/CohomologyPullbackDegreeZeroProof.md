# Degree-zero normalization of canonical relative-cohomology pullback

The theorem `relativeCohomologyPullbackDegreeZeroStatement` proves exactly
`RelativeCohomologyPullbackDegreeZeroStatement.{u}` from
`CohomologyPullbackLawsStatement`. For every commutative ring `R`, schemes
`X` and `Y` over `Spec R`, morphism `h : Y ⟶ X`, and actual
structure-sheaf module `M` on `X`, the actual map
`relativeCohomologyPullback h M 0`, followed by the forward
`relativeCohomologyZeroIso` on `Y`, equals the forward comparison on `X`
followed by `relativeGlobalSectionsPullback h M`. There are no additional
geometric, flatness, or acyclicity hypotheses.

This is an internal normalization result for the unchanged constructions in
`CohomologyPullback`, `CohomologyPullbackSections`, `DerivedSections`, and
`DerivedPlus`. Its provenance is those definitions and Mathlib's derived
functor, single-complex, cycles, and extension-by-zero comparisons. It proves
the degree-zero component of the five-law target; the full conjunction still
requires its other components. It does not assert a formal comparison with
another implementation of the general Stacks cohomological f-map.

The first part of the Lean file works for an additive functor `F` between
abelian categories, with enough injectives in its source and the indicated
derived categories.

1. The shared `singlePlus` from
   [`DerivedPlusZero`](../../Cohomology/DerivedPlusZero.md), together with
   `singlePlusIso` and `singleImageIso`, records the
   single-complex and termwise-functor comparisons. `augmentationPlus`
   is the chosen resolution augmentation viewed in bounded below complexes.
   Naturality of the localization comparison proves
   `singlePlusIso_comp_augmentation`.
2. `zeroUnit` applies the actual `rightDerivedFunctorPlusUnit` to the
   single complex, with these comparisons. Naturality of that unit gives
   `zeroUnit_comp_derivedComplexIso`: after transport to a chosen injective
   resolution, it is localization of `F` applied to the augmentation.
3. `qHomologyIso` compares derived-category homology of a localized
   bounded below complex with its ordinary homology. Its naturality follows
   from the localization and homology-factorization natural isomorphisms.
   `single_homology_extend_zero` computes homology of a map from a single
   complex into an extended natural-indexed complex: if its degree-zero
   head is a specified map into cycles followed by the cycles inclusion,
   its homology map is that map followed by the homology projection.
   The proof uses naturality of the homology projection and the published
   cycles and homology comparisons for extension by zero.
4. `mapExtendIso_inv_f_comp_extendXIso` and its forward counterpart
   identify the termwise extension comparison at an index in the
   embedding. The calculation reduces to identities at that index.
5. `zeroUnitHomology` transports `zeroUnit` through the canonical
   degree-zero homology of the single complex.
   `zeroUnitHomology_comp_homologyResolutionIso` applies the preceding
   naturality equation. Then `zeroUnitHomology_comp_homologyIso`
   uses the single-complex calculation and the head of the actual
   resolution augmentation to identify the result with Mathlib's
   `F.toRightDerivedZero.app M`. The last comparison is precisely
   `InjectiveResolution.toRightDerivedZero_eq`, including
   `isoRightDerivedObj`; it is not a new choice of the zeroth comparison.

The scheme-module part applies this calculation to the actual pullback.
`pullbackAugmentationPlus` is the published
`pullbackResolutionAugmentation` viewed in bounded below complexes.
`pullbackDerivedAugmentation_eq_singlePlus` identifies its localization
with the published derived augmentation, by the faithful inclusion into the
derived category and naturality of the localization comparison.
`pullbackResolutionAugmentation_head` computes its head: it is the actual
pullback/pushforward adjunction unit followed by the pushforward of the
chosen injective-resolution augmentation.

`pullbackSectionsAugmentationPlus` applies relative sections to this
augmentation and then the actual `pullbackSectionsComplexIso`.
`zeroUnit_comp_relativeDerivedSectionsPullback` follows the four defining
factors of the actual derived pullback. Naturality of the actual derived
unit moves it through the augmentation, and its inverse cancels on the
pushed-forward resolution. The needed invertibility follows from the
published `pushforwardInjectiveAcyclic` on the injective resolution terms
and `acyclicTermsDerivedUnitStatement`; no acyclicity of `M` is assumed.
Taking homology gives
`zeroUnitHomology_comp_pullback_homologyResolutionIso`.

`pullbackSectionsComplexIso_hom_f` identifies the complex comparison
component with `relativePushforwardSectionsIso`.
`pullbackSectionsAugmentationPlus_head` then uses naturality of this
isomorphism, first at the extension comparison and then at the resolution
augmentation. Together with the preceding head calculation, this makes the
head on sections equal to `relativeGlobalSectionsPullback h M` followed by
sections of the augmentation on `Y`.

Finally, `zeroUnitHomology_comp_pullback_homologyIso` applies
`single_homology_extend_zero` to that head. Its map into cycles is
`relativeGlobalSectionsPullback h M` followed by the target resolution's
`toRightDerivedZero'`. Transport through `isoRightDerivedObj` gives the
target `toRightDerivedZero`. The source normalization therefore yields
`toRightDerivedZero_comp_relativeCohomologyPullback`. Since relative
sections preserve finite limits, Mathlib identifies their zeroth right
derived functor with themselves: `rightDerivedZeroIsoSelf` is the inverse
of `toRightDerivedZero`. Cancelling the source isomorphism and using the
target inverse identity proves the exact published degree-zero law.
