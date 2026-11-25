# Full pullbacks of small actual affinoid spectra

This internal construction proves the full categorical universal property for
the small realization of the actual closed-quotient affinoid pushout. The field
universe `u` and space universe `v` are independent. The coefficient field is
complete and ultrametric, and every saturated presentation constructed here has
space and atlas-index universes `v`.

For bounded maps `f : A → B` and `g : A → C` between presented affinoid
algebras, the small-spectrum construction supplies the saturated realizations
of `A`, `B`, and `C`. The main square also assumes that the spectrum of the
actual `AffinoidPushout.algebra f g` is small in `v`. Its object and projections
are the existing `pushout`, `pushoutFst`, and `pushoutSnd` from
`SmallAffinoidPointwiseSquare`. The square uses the original bounded pushout
maps and their complete saturated extensions.

`topIndex` is the retained original whole-spectrum chart in the saturation.
`range_topIndex` proves that its range is the entire small ambient spectrum,
using the retained original range and the canonical spectrum homeomorphism.
Consequently `top_contains` places every saturated chart inside it.
`top_algebra` identifies its presented algebra with the original algebra.
`map_pullbackAtTop_heq` applies retention of original pullbacks under coherent
saturation: the complete bounded pullback at the two retained charts is
heterogeneously equal to the input map. This retains the bounded algebra map,
including its behavior on nilpotents.

The private transport lemma eliminates four algebra equalities and the four
heterogeneous map equalities, then applies the actual affinoid pushout's
`existsUnique_lift`. `pushout_topChartPushout` uses it to establish the bounded
universal property at the greatest charts of this specific square. This
property quantifies over every presented affinoid test algebra and every
compatible pair of bounded algebra maps.

`pushout_isPullback` combines that property with the existing complete strong
commuting equation. The greatest-chart construction lifts a strong cone
chartwise by bounded-algebra universality; bounded uniqueness proves
compatibility with source restrictions. Local chart reconstruction supplies
the ambient map and all admissible pullbacks. It also proves both projection
equations and uniqueness of the entire strong morphism. Thus this is the
ordinary categorical `IsPullback`, with every saturated test presentation and
every complete strong cone allowed. Test sources need no greatest chart.

`pushout_isRefinedStrongPullback` uses the same unique strong lift and the
identity quasi-isomorphism as source refinement. Its uniqueness clause is
joint uniqueness of complete strong maps. The existing fraction descent
theorem then proves `pushout_localized_isPullback`. This universal property
ranges over all objects and morphisms of the actual localization, including
arbitrary right fractions. The pullback object and its universes are unchanged.
No uniqueness assertion about ordinary point pairs is needed or made.

The final two existence theorems replace the supplied pushout-smallness
instance by the explicit premises `FiniteBanachPushoutStatement K` and
`f.IsFiniteBanach`. The existing finite-fibre smallness consequence supplies
the missing instance in universe `v`. `exists_finite_isPullback` packages the
actual strong pullback and its refined property;
`exists_finite_localized_isPullback` packages the actual localized pullback.
The finite Banach pushout proposition remains a premise.

The provenance is internal: this specializes the greatest-chart pullback
construction using the closed-quotient affinoid pushout, the small singleton
spectrum realization, original-chart retention under saturation, and full
localized fraction descent. No external statement is transcribed. This module
asserts no etaleness of a projection and provides no global gluing construction.
Unrestricted localized etale pullback existence is proved in
`LocalizedEtalePullbackExistence` (`exists_localizedPullback_of_etale`), and
etale base change, for Hausdorff saturated presentations whose space and
index universes are the field universe `u`, as `etaleBaseChange` in
`EtaleBaseChangeProof`.
