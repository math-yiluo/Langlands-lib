# Full strong restriction to an actual source chart domain

Author: Worker 36.

This derived unit works with supplied actual indexed affinoid atlases over a
complete ultrametric normed field. It preserves the independent coefficient,
ambient-space and original chart-index universes `u`, `v` and `w`. The algebras
are the original presented positive-polyradius affinoid algebras and every
pullback is a bounded algebra homomorphism. No reducedness assumption is used.

The convention comes from Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Definition 1.2.3 and Remark 1.2.4(i), printed p.16 /
PDF p.13, and Definition 1.2.7, printed p.18 / PDF p.15. Registered source:
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Those pages were reread for this unit. Original chart domains have their
original affinoid algebras and bounded domain restrictions; a strong morphism
has a compatible affinoid morphism at every admissible chart pair. Source
restriction and the equality and composition consequences below are derived
from these conventions and the published actual chart-domain construction.
They are not separately numbered assertions in the source.

`StrongHom.restrictSource f i` restricts only the source of `f` to the actual
subspace of original chart `i`. The source atlas retains every original
chart contained in `i`. The entire original target atlas remains available.
Its continuous map is `f.baseMap` after the actual subspace inclusion.
`restrictSource_admissible_iff` identifies local admissibility for source
subchart `c` and target chart `j` with original admissibility for `c.val,j`.
It follows by expanding images of the original charts and forgetting the
subtype. Each bounded pullback, chart square and two-variable naturality
equation is the corresponding original datum. This construction requires
neither directedness nor a target-chart choice.

`pullback_congr` evaluates equality of full strong maps at a fixed admissible
pair, permitting different proofs of admissibility. It follows by substitution
and proof irrelevance. `ext_of_restrictSource` proves that the family of full
source-chart restrictions determines the global map, without directedness.
Original chart coverage first gives equality of the continuous maps. For any
original admissible pair `i,j`, evaluate the equality of source restrictions
at their whole source chart and original target chart `j`. This gives equality
of the original bounded pullbacks, and strong-map extensionality finishes.
Equality on spectrum points is used only for the ambient continuous maps;
it is not used to identify bounded algebra homomorphisms.

`restrictSource_compOfDirected` proves that source restriction commutes with
the published full directed composite. It assumes directed intermediate and
target atlases and no directedness of the source. For each original source
subchart, choose an admissible intermediate and target chart using the two
strong maps. The exact bounded-composition formula gives the same bounded
composite on both sides. Published directed extensionality recovers all
admissible bounded maps.

`chartStrongInclusion A i` is the source restriction of the identity. It has
the actual subspace inclusion as its continuous map and the original bounded
restrictions at every admissible pair. It exists without a directed ambient
atlas. If the ambient atlas is directed,
`chartStrongInclusion_eq_ofDirected` identifies it with the published full
extension of the original chosen inclusion: the selected bounded maps are
identities by the atlas restriction-identity law.
`chartStrongInclusion_comp` derives its factorization with any global strong
map from restriction of directed composition and the identity law.

`chartStrongMap_comp_restrictSource` proves that nested original chart
inclusion followed by the larger source restriction equals the smaller
source restriction when the target is directed. The actual intermediate
chart-domain atlas has a greatest chart and is therefore directed. For a
source subchart, use that same original chart inside the larger domain as
the intermediate chart. Its bounded inclusion map is the identity, so the
directed bounded-composition formula reduces to the original pullback.

`onCharts_comp_chartStrongInclusion` compares the existing simultaneous
source/target restriction with the new source-only restriction. At any
admissible pair, compose the former with the actual target chart inclusion.
The target ambient atlas is directed; its chart-domain atlas has a greatest
chart. The bounded composite through that whole target chart is the original
pullback followed by the identity, and directed extensionality recovers the
complete equality.

These constructions concern the supplied original atlases and their actual
chart domains. General atlas extension, finite algebraic gluing, unrestricted
strong composition and localization, structure sheaves, étale and equivariant
sites, and the Harris tower remain separate obligations.
