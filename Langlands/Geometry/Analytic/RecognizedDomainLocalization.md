# Recognition and actual localized domain diagrams

Author: Worker 36.

This module constructs a natural isomorphism between the localized diagrams
of actual domain presentations for an arbitrary affinoid atlas and its
constructed recognition extension. The index comparison retains each
literal subset. Each component comes from the actual compatible recognition
map restricted to that subset, with its full bounded pullback family. Both
directions of the component isomorphism induce the identity continuous map.
The comparison also commutes with the canonical ambient domain inclusions.

The source conventions are Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Definitions 1.2.7 and 1.2.9, printed pp.18–19 /
PDF pp.15–16, for all-admissible compatible strong maps and full
quasi-isomorphisms; the category-of-fractions paragraph, printed p.20 /
PDF p.17; Proposition 1.2.13(ii), printed p.21 / PDF p.18, for the
constructed recognition extension; and Definition 1.3.1 and the following
domain paragraph, printed p.23 / PDF p.20, for the contained-chart domain
atlas and its canonical inclusion. Registered source
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These original pages were read for this unit. No source-specific errata
file was found in the available project and Library locations.

This is a derived construction from `RecognizedAtlasLocalization`,
`RecognizedDomainSite`, `CompatibleDomainRestriction` and the existing
localization of compatible strong maps. It is not a separately numbered
source theorem. It makes the domain presentation comparison, rather than
only the domain order or its sheaf categories, explicit.

For `A : AffinoidAtlasPresentation K`, the source `A.saturationSource`
is the original atlas with canonically lifted indices. It does not
assume that the original atlas already contains all affinoid domains.
`A.recognitionTarget` is the constructed recognition atlas, also
reindexed. Both use exactly `A.space`, and both index universes are
`max v w`; no equality of the original space and index universes is
required.

`isOriginalChartDomain_reindex_iff` proves that reindexing changes no
domain condition: the set of chart ranges is equal. Combining this with
the previously proved recognition-domain equivalence yields
`recognitionTarget_isOriginalChartDomain_iff` and
`recognitionLiftedDomainOrderIso`. Both directions retain the literal
subset and change only its domain proof. The carrier formula is
definitionally reflexive.

`compatibleToRecognition_hasDomainTargets` constructs the containing
target chart needed to restrict the strong map. For every original
source chart contained in the domain, its original recognition index
has exactly that same range and is therefore contained in the domain
on the target side. No choice of bounded maps or domain comparison is
supplied as a hypothesis.

`compatibleDomainToRecognition` applies the actual compatible domain
restriction construction to the same subset on both sides. The
continuous map is the identity on its induced subspace. Every admissible
bounded pullback is the original one, as in the imported restriction
construction. `compatibleDomainToRecognition_isQuasiIso` restricts the
proved ambient full quasi-isomorphism; the domain image is exactly the
same subset, and the preceding target-chart witnesses discharge the
only additional chart condition. In particular, the affinoid-domain
identification holds for every admissible pair, not just a chosen pair.

`compatibleRecognitionDomainComparison` assembles these actual maps
into a natural transformation of compatible domain diagrams, reindexing
the target diagram by `recognitionLiftedDomainOrderIso.equivalence`.
Naturality applies the complete nested restriction theorem to the
same source and target inclusions. It is equality of compatible
morphisms, including their bounded maps and coefficient coherence.

`localizedRecognitionDomainIso` inverts the proved component
quasi-isomorphism in the existing category of fractions.
`localizedRecognitionDomainNatIso` assembles these isomorphisms using
`NatIso.ofComponents`. Its forward naturality follows by applying the
localization functor to the raw naturality equality and using
functorial composition on each side. The hom and inverse component
formulas identify precisely those constructed component isomorphisms.

`localizedRecognitionDomainIso_hom_space` follows from the descended
space functor on a localized original map. The inverse-space formula
applies that functor to the isomorphism's `hom_inv_id`, uses functorial
composition and identity, and cancels the already identified identity
forward map. The inverse is a morphism in the constructed localization;
an inverse raw strong map is not required.

`compatibleRecognitionDomain_inclusion` compares the two paths from
the source domain to the ambient recognition presentation. For each
source chart, choose its contained admissible target chart, compute
both composite bounded pullbacks, and use the original self-restriction
identities. Full compatible extensionality gives the equality.
`localizedRecognitionDomain_inclusion` applies the localization
functor to that equality. Its ambient horizontal arrow is the
previously constructed `localizedRecognitionIso.hom`.

The coefficient field is complete and ultrametric; its valuation need
not be nontrivial. Empty domains, zero algebras and nonreduced algebras
remain allowed. Applying the construction to
`a.saturatedPresentation` gives the same diagram comparison for the
full local-domain atlas and its recognition extension. This does not
identify all domains of that enlarged atlas with the original-chart
domains of the input `a`.

The unit does not identify structure sheaves or their bounded
restrictions, prove unrestricted analytic-domain factorization,
construct an étale site, or establish maximal recognition closure,
idempotence or invariance under arbitrary equivalent full nets.
Neither the special-intersection statement nor closed-ideal
effectiveness is assumed.
