# Spectral effectiveness from original bounded base-change comparisons

This internal derived construction separates the spectral consequences of
canonical original bounded base-change equivalences from the analytic descent
obligation that produces those equivalences and a matching presentation.
It does not prove unrestricted finite Banach algebra descent by itself.

Given a matching presentation, `originalDomain` uses the existing full-domain
base-change theorem to represent the exact inverse image of each original
cover locus by the actual original closed-quotient base change. Its structural
map uses the stored cover restriction, which equals the domain's structural
map because the cover targets the whole spectrum. A supplied bounded comparison
equivalence then gives `localSpectrumEquivOfComparison` by composing its
contravariant spectrum homeomorphism with the full domain's locus
homeomorphism. The theorem `localSpectrumEquivOfComparison_eq` uses the equality
of the entire forward comparison map and its left-leg equation to identify
this homeomorphism with the target's prescribed local spectrum map.

`overlapCompatible` proves the entire comparison-map compatibility by the
pushout universal property. On the global leg it is the defining matching
projection equation; on the intersection coefficient leg it is the supplied
transition's equality on the entire coefficient algebra. No effectiveness
hypothesis is needed for this compatibility.

`spectrumMap_surjective_of_comparison` uses the original cover to choose an
index over each point of the presented spectrum, then uses the corresponding
local homeomorphism to lift that point. For injectivity,
`overlapRelation_of_spectrum_eq` starts with two local points having the same
global image. Their common base point belongs to the literal intersection.
The full intersection representation supplies a point over it, and injectivity
of the original base-domain spectrum map makes that point compatible with
the second local point. `AffinoidPushout.exists_point` lifts them to the actual
second local overlap quotient. The whole matching equation says its two
local images have the same global image; injectivity of the first local
full-domain spectrum map identifies its first image with the prescribed first
point. Thus the two original points are related by an actual generating
overlap relation. Quotient induction now proves injectivity of the canonical
gluing map.

`spectrumEquivOfComparison` uses this bijection and continuity to construct
the global homeomorphism. The finite disjoint union of local spectra is
compact, hence its quotient is compact; the presented algebra's spectrum is
Hausdorff. The forward map is definitionally the prescribed canonical map,
as recorded by `spectrumEquivOfComparison_eq`. There is no separate ambient
Hausdorff assumption. Identity and triple-cocycle conditions are unnecessary
for these conditional consequences: the pairwise matching equations and the
original comparison effectiveness already imply them.

These are formal consequences of the published definitions and full-domain
base-change and spectrum-embedding theorems. They address the explicit
spectral output in the derived formulation of Berkovich 1993, Lemma 1.2.12,
printed p.20 / PDF p.17, rather than supplying its finite Banach module
descent input. The original source registration is
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Arbitrary positive polyradii, trivial valuations, and empty spectra are retained.
