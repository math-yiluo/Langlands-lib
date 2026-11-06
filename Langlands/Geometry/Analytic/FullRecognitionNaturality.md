# Full bounded naturality of recognition idempotence

Author: Worker 36.

This module constructs the functor from iterated full-recognition charts to
their earlier full-recognition presentations. It proves that the already
constructed pointwise bounded algebra equivalences intertwine every literal
inclusion's entire bounded restriction. Equality is established on arbitrary
algebra elements through actual finite full-domain covers.

## Source and provenance

The motivation is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), the canonical bounded restrictions in Proposition 1.2.13(ii)
and the flattening of successive finite special covers in part (iii),
printed p.21 / PDF p.18. Registered source
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original passage was read. No source-specific errata file was found in
the available project and Library locations.

The result is derived infrastructure for that recognition construction.
`FullRecognitionIdempotence` constructs an earlier recognized index for
every iterated chart, with a bounded algebra equivalence and exact ambient
chart formula. This module supplies the full naturality of those specific
comparisons, using `NestedRecognitionOriginalDomains`, finite subordinate
covers, equalizer restriction laws and full-domain separation. The source
does not state these internal Lean functor and comparison names.

## Conventions

Let `a` be the actual indexed affinoid atlas and let
`B = a.fullRecognitionAtlas`. The earlier recognized inclusion category has
objects `a.saturatedAtlas.RecognizedSubset`, which are the indices of `B`.
The iterated category has objects
`B.saturatedAtlas.RecognizedSubset`. Morphisms are literal inclusions;
each has its previously constructed contravariant bounded algebra map.
For an iterated object `W`, write `F(W)` for
`a.fullRecognitionIdempotenceIndex W` and
`e_W : W.algebra ≃ F(W).algebra` for the constructed bounded equivalence.
Both objects have the identical literal ambient locus.

## Recovery of original restrictions

`recognitionChartDomain_comp_restriction` is generic in an atlas before
saturation. For nested outer recognized parents `U ⊆ V` and any original
chart `s` contained in `U`, its canonical full-domain map satisfies
`r_s^U.comp (U.restriction V) = r_s^V`. The proof exposes the three actual
bounded structural factors, applies the outer original-restriction
composition law and composes with the fixed original-to-saturated maps.

`RecognizedSubset.originalRestriction_comp_affinoidRealization` is also
generic. Given any actual finite gluing datum `d` realizing the same locus
as a recognized object `V`, and its actual affinoid realization `c`, it
identifies restriction through the constructed realization-to-recognized
algebra equivalence with `d.originalRestriction s` composed with
`c.restrictFromParent`. It covers every contained original chart `s`.
The proof cancels the recognized presentation equivalence and applies
`originalRestriction_comp_restrictionTo` to the defining-cover comparison.
The Hausdorff assumption is only on the realized locus.

`iteratedRecognition_originalRestriction` applies this framework to the
finite gluing datum constructed for an iterated chart `W`. For every
first-saturation original chart `s` contained in `W`, it proves that the
realized equalizer restriction is exactly the canonical nested
`recognitionChartDomain` map. The realized locus is Hausdorff by its actual
affinoid homeomorphism. `subordinateCoverOfHausdorff` constructs a finite
full-domain cover of `s` subordinate to the defining components. Its
`domainCover.algebra_ext_of_restrict_eq` separates arbitrary elements of
`s.algebra`. On each subordinate child, the equalizer original-restriction
law and the canonical original-chart naturality law compare both maps to
the same defining-component map. No assumption that spectra detect algebra
maps is used.

`fullRecognitionIdempotenceAlgebraEquiv_originalRestriction` combines the
two recovery results. For every such original chart `s`,
`F(W).originalRestriction s` composed with `e_W` equals the canonical
nested original-chart map from `W`. This includes charts outside the
chosen defining cover of `F(W)`.

## Complete naturality and the constructed functor

`fullRecognitionIdempotenceAlgebraEquiv_naturality` proves, for every
iterated inclusion `U ⊆ V`,

```
e_U.comp (U.restriction V) = (F(U).restriction F(V)).comp e_V.
```

The proof separates arbitrary algebra elements by `F(U).componentCover`.
Each component's full structural map is its canonical original
restriction. The recovery result, outer-parent naturality and the earlier
original-restriction composition law then identify the two composites on
each component. Thus the result is equality of complete bounded maps,
including all nonreduced information.

`fullRecognitionIdempotenceFunctor` constructs the actual functor `F` on
these inclusion categories. Its object map is the previously constructed
earlier index; its arrow map uses the unchanged literal subset inclusion.
`fullRecognitionIdempotenceFunctor_locus` records equality of object loci.
`fullRecognitionIdempotenceFunctor_naturality` states the preceding full
bounded equation using this functor's actual arrows. The two functor laws
hold by the construction of the thin inclusion categories.

## Scope

The field is complete, normed and ultrametric. The field, ambient space and
original index universes are independent. No nontrivial valuation, global
Hausdorffness, reducedness, nonzero algebra or nonempty cover premise is
added. The output functor and full bounded comparisons are constructed
from the input atlas; they are not supplied as hypotheses.

This module does not yet construct inverse functors or an affine-diagram
natural isomorphism. Arbitrary equivalent-net invariance, maximal-atlas
uniqueness, unrestricted analytic morphism comparison, analytic etale sites
and the Harris specialization remain further obligations.
