# The constructed affinoid atlas on all local full domains

This module constructs the enlarged atlas in Berkovich, *Etale cohomology for
non-Archimedean analytic spaces* (1993), Proposition 1.2.6, printed pp.17-18
(PDF pp.14-15). The input is an arbitrary indexed affinoid atlas over a complete
ultrametric normed field. The enlarged family is the constructed net of all
subsets that are full affinoid domains in one original chart. No directedness
or greatest chart is assumed.

`originalSaturatedIndex` includes each original chart domain as a literal member
of this family. For each member, `saturatedRepresentative` chooses an actual
local full-domain presentation. When the member is an original chart domain,
it chooses the whole-spectrum domain in that original chart. Original
chart-domain injectivity proves `saturatedRepresentative_original`, so
the selected presentation on every original chart is precisely that original
whole-chart presentation. For all members, `saturatedRepresentative_locus`
proves equality with the prescribed ambient subset.

`saturatedChart` is the chosen presentation's actual spectrum embedding.
Its range is the indexed subset, and the family of all such ranges is exactly
the enlarged local-domain family. This gives a bijective indexing by actual
subsets, even when several local full-domain presentations represent the same
subset.

`saturatedInclusion` is the actual constructed local-domain arrow for any
containment of chosen chart ranges. Its bounded map gives the new atlas
restriction, its ambient spectrum equation gives chart compatibility, and its
full represented-domain property gives unique bounded factorization against
every presented affinoid test. The proved uniqueness of these actual arrows
gives the bounded identity and composition equations.

`saturatedAtlas` stores these actual algebras, embeddings, bounded restrictions
and full-test universal properties. The enlarged net was constructed in the
preceding module, and local Hausdorffness is inherited from the original
ambient space. Its chart-index universe is the ambient subset universe; the
original chart-index universe remains independent.
The displayed algebra, chart and chart-family formulas identify this data
exactly. Every original chart domain remains present, and its algebra is the
original actual algebra.

`localDomainSaturatedEquiv` gives an actual bounded algebra equivalence between
every local-domain presentation and the presentation selected for its ambient
subset. It uses the proved equal-locus comparison in the unrestricted
local-domain category and retains both complete bounded maps.

The proof implements the presentation-choice and bounded-restriction
construction of Proposition 1.2.6 using the previously constructed actual
full-domain restrictions, their full test representation and coherence, and
the enlarged net. It does not supply any of these analytic outputs as input.
Arbitrary positive polyradii, trivial valuations, nonreduced or zero quotients
and empty permitted covers remain included. The explicit full strong comparison
with the original atlas, independence of all presentation choices as a full atlas
comparison, strong morphism extension and composition, analytic or equivariant
sites and the Harris tower remain further work.
