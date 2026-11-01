# Coefficient naturality of canonical relative cohomology pullback

This module proves the published proposition
`Langlands.AlgebraicGeometry.Modules.DerivedSections.RelativeCohomologyPullbackCoefficientNaturalityStatement`
by the theorem `relativeCohomologyPullbackCoefficientNaturalityStatement` in the
same namespace. It holds at arbitrary universe `u`, for every commutative
base ring, morphism of actual schemes over its spectrum, actual module
morphism, and natural degree, including zero. It adds no assumptions to the
published statement and uses the published `relativeCohomologyPullback`.
This is one component of the five-law task; it does not prove identity,
composition, degree-zero normalization, or split retraction.

The provenance is internal: coefficient naturality is the coherence obligation
of the existing resolution-based construction. The proof uses the Library
construction and its generic `DerivedPlusNaturality` comparisons. It does not
claim a new identification with a separate implementation of the Stacks
Project f-map, and uses no external source beyond the published interfaces.

The proof first establishes `AcyclicResolution.mapAugmentation_naturality_hom` for
an additive functor and an augmentation-compatible morphism of injective
resolutions. The suffix distinguishes this bundled-morphism helper from the
existing raw-cochain-map theorem `mapAugmentation_naturality` in
`CohomologyBaseChange`; both interfaces remain available.
Maps from a single complex agree if they agree in degree zero;
there the assertion is the defining compatibility of the resolution morphism
mapped by the functor. A second helper,
`DerivedPlus.extendSingleIso_inv_naturality`, identifies the single complex
in degree zero with its extension from natural to integer degrees, naturally
in the coefficient object. Its proof again uses the zero component and
cancellation of the extension isomorphisms.

`pullbackResolutionAugmentation_naturality` combines these two lemmas with
naturality of the actual pullback/pushforward adjunction unit. It applies
extension to the resulting equation and then uses the existing naturality
of `DerivedPlus.mapExtendIso`. Consequently it respects the full
integer-indexed pushforward resolution used by the construction.
`pullbackDerivedAugmentation_naturality` transports this equality to the
bounded below derived category by its faithful inclusion into the unbounded
derived category, using the natural single-complex and localization
comparisons.

The termwise sections comparison is natural by
`Functor.mapHomologicalComplexCompIso`. The lemma
`isIso_unit_pushforward_resolution` records the applicability of the existing
acyclic-terms derived-unit theorem to a pushed-forward injective resolution.
Its hypotheses are discharged by the existing theorem that pushforwards of
injective scheme modules are acyclic for relative sections. This is a proved
input of the published construction, rather than an additional hypothesis on
the schemes or coefficients.

For `relativeDerivedSectionsPullback_naturality`, choose a morphism of
injective resolutions lifting the pulled-back coefficient morphism, using
`DerivedPlus.descHom`. Naturality of the derived augmentation, the inverse
derived unit, the termwise sections isomorphism, and the inverse
`DerivedPlus.derivedComplexIso` gives the desired derived-category square.
Finally `relativeCohomologyPullback_naturality` applies the homology functor
and conjugates by the natural `DerivedPlus.homologyIso` comparisons. This is
exactly the square defining the published coefficient-naturality proposition.

Worker 310 implemented the proof. Worker 152 supplied the direct naturality
argument for the termwise sections comparison.
