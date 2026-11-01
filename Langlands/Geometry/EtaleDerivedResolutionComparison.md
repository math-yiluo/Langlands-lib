# Actual resolution comparison for geometric etale pullback

This internal construction compares actual geometric derived global-section
pullback with the ordinary section square on an actual injective resolution.
The morphism `f : Z ⟶ X` is etale. Schemes, the commutative coefficient ring
`R`, and the module carriers lie in universe `u`. The sheaf-derived
localizations have independent morphism universes `wX` and `wZ`; derived
coefficient modules use `wR`. There are no additional finiteness, field,
Noetherian or local-constancy hypotheses.

Write `L = inverseImage f R` for the constructed geometric inverse image,
`ΓX` and `ΓZ` for actual small-etale module-sheaf global sections, and
`a = sectionsPullback f R : ΓX ⟶ L ⋙ ΓZ` for their map from the geometric
adjunction. Given an actual injective resolution `I` of a sheaf `F`, write
`J = mapInjectiveResolution L I`. The terms, augmentation and injectivity
of `J` are constructed. In particular, injective preservation of `L` is
proved by comparison with etale restriction, rather than assumed.

`sectionsComplexPullback_resolution` proves equality of two actual maps of
bounded-below complexes. One applies geometric section pullback to the integer
extension of `I`, identifies the image resolution with `J`, and applies the
section-extension comparison on `Z`. The other applies the section-extension
comparison on `X`, then the extended ordinary degreewise square `a` on `I`.
Its proof passes through the faithful inclusion of bounded-below complexes
into all complexes, identifies the underlying geometric map degree by degree,
and uses the existing natural-transformation and composition laws for extension
by zero. The private helper identifies the underlying extension-comparison map;
it introduces no extra input.

`plusSingleIso_resolution` identifies two maps from geometric inverse image
of the degree-zero derived singleton of `F` to the localization of `J`.
One applies inverse image to the singleton-to-resolution isomorphism, then
uses the localization factor and mapped-resolution complex comparison.
The other uses the derived singleton comparison and the actual augmentation
of `J`. The proof applies the faithful inclusion into the unbounded derived
category, identifies the localized augmentations, and uses the proved
`localizedMappedResolutionIso_augmentation`. This result needs `wX` and `wZ`,
but no localization of coefficient modules.

Let `cI` and `cJ` denote the actual `imageResolutionIso` comparisons from
derived sections of `F` and `L(F)` to the localizations of `ΓX(I)` and
`ΓZ(J)`. Let `sI` be the actual `imageResolutionSquare ΓX L ΓZ a I`.
Then `sheafDerivedPullback_resolution` proves

```text
sheafDerivedPullback(f,R)_F ≫ cJ.hom = cI.hom ≫ Q(sI).
```

This is a statement about the already constructed pullback from the derived
inverse/direct-image adjunction. Its proof moves the singleton-to-resolution
map through derived pullback by naturality, uses the singleton augmentation
comparison just proved, and applies derived-pullback normalization. Naturality
of the target right-derived section unit then reduces the equation to
`sectionsComplexPullback_resolution`. The section-unit components on the
injective resolutions are isomorphisms, which permits the cancellations.

`sheafDerivedPullbackResolutionIso` packages this commuting square as an
actual isomorphism in the arrow category of bounded-below derived coefficient
modules. Its source is the geometric sheaf-derived pullback arrow and its target
is `Q(sI)`. Its left and right endpoint isomorphisms are precisely `cI` and `cJ`.
The proved resolution equation supplies the commuting-square field; Mathlib's
`Arrow.isoMk` constructs the inverse and isomorphism laws.

Finally, `sheafDerivedPullback_eq_derivedMap` proves equality of natural
transformations

```text
sheafDerivedPullback f R =
  derivedMap ΓX L ΓZ (sectionsPullback f R).
```

The right side is the existing mapped-resolution construction for the same
geometric inverse image and ordinary section map. The proof evaluates at each
coefficient sheaf, uses its actual chosen injective resolution, expands the
resolution formula for `derivedMap`, cancels the target comparison isomorphism,
and applies `sheafDerivedPullback_resolution`. The desired comparison is
therefore proved, not supplied as data.

The provenance is internal categorical specialization of the existing actual
geometric, extension-by-zero, injective-resolution and derived-localization
constructions. No external literature theorem is asserted here. Agreement with
the older restriction-based `EtalePullback.derivedSectionsMap` still requires
transport through `inverseImageIsoRestriction`; that agreement and its
cohomology consequence are separate. Compact supports, scalar coherence,
smooth equivariant actions and Harris specialization also remain separate
obligations. This group does not complete the full Harris framework.
