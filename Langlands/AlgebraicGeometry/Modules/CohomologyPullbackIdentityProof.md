# Identity law for canonical relative-cohomology pullback

The theorem `relativeCohomologyPullbackIdentityStatement` proves the published
`RelativeCohomologyPullbackIdentityStatement.{u}`. For every commutative base
ring `R`, scheme `X` over `Spec R`, actual structure-sheaf module `M` on `X`,
and natural degree `n`, the actual `relativeCohomologyPullback (𝟙 X) M n`,
followed by cohomology of the forward `Scheme.Modules.pullbackId`
identification, is the identity. This includes degree zero and adds no
geometric or acyclicity hypothesis.

This is an internal coherence proof for the construction in
`CohomologyPullback`, using the exact identity comparison fixed in
`CohomologyPullbackLawsStatement`. It proves one component of the five-law
target. Composition, coefficient naturality, degree-zero normalization, and
split retraction are separate obligations. It does not assert an additional
formal comparison with a different implementation of the general Stacks
cohomological f-map.

The proof follows the four factors of the published derived pullback.

1. `pullbackIdentity_unit` uses Mathlib's mate relation between `pullbackId`
   and `pushforwardId` and naturality of `pushforwardId`. The identity
   adjunction unit, followed by `pushforwardId`, is the inverse coefficient
   identification `pullbackId.inv`.
2. `pushforwardIdentityCochainIso` applies `pushforwardId` term by term.
   `pushforwardIdentity_mapExtend` shows that this comparison commutes with
   extension by zero: at an index in the embedding it is an identity
   calculation, and outside the embedding its source is zero.
   `pullbackIdentity_natAugmentation` compares the natural-indexed
   augmentation using the preceding unit equation.
   `pullbackIdentity_resolutionAugmentation` then extends this equation to
   the integer-indexed resolution. Naturality of the inverse
   `extendSingleIso` is proved by the degree-zero component, using the
   argument contributed by Worker 310.
3. `pullbackIdentity_derivedAugmentation` transports the augmentation
   equation through localization. It uses the faithful inclusion from the
   bounded below derived category, naturality of the single-complex and
   localization comparisons, and the published formula for
   `singleIsoOfResolution`.
4. `pullbackIdentity_sections` identifies the actual
   `relativePushforwardSectionsIso (𝟙 X)` with relative sections applied to
   `pushforwardId`. On each open set the pushforward-composition and
   identity maps are identities, and the congruence map restricts along an
   identity. `pullbackIdentity_sectionsComplex` applies the equation
   termwise.

`relativeDerivedSectionsPullback_identity` combines these comparisons with
naturality of `rightDerivedFunctorPlusUnit`. The needed invertibility on
the pushed-forward injective resolution follows from the published
`pushforwardInjectiveAcyclic` and `acyclicTermsDerivedUnitStatement`, rather
than an assumption on `M`. The middle factors become the forward
`derivedComplexIso`; they cancel its inverse, leaving the derived-complex
map of `pullbackId.inv`.

Finally, `relativeCohomologyPullback_identity` uses the published
`DerivedPlus.homologyIso_hom_naturality` to identify this map on homology
with classical relative cohomology of `pullbackId.inv`. Functoriality and
the inverse/forward coefficient identities give the required identity.
The concluding theorem has exactly the published component proposition
as its type.
