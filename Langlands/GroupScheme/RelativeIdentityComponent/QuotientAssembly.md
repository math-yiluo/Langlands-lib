# Group structure on supplied identity-component quotients

This internal construction starts with a group scheme `G` smooth over an
arbitrary scheme `S`, an inclusion `i : H → G` satisfying
`IsRelativeIdentityComponent G i`, and supplied data
`D : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i`.

`homogeneousQuotientGroupScheme hi D` is the group scheme on the supplied
quotient scheme. `homogeneousQuotientProjection hi D` is the supplied
projection as a group homomorphism. Its underlying morphism over `S` is
exactly `D.projection`, as stated by
`homogeneousQuotientProjection_hom`.

The construction obtains normality of the relative identity component
from the published `RelativeIdentityComponent.smoothNormality`. It then
uses `D.groupScheme` and `D.groupProjection` from
`HomogeneousQuotientGroup`. The theorem
`homogeneousQuotientProjection_isFppfQuotient` applies the corresponding
published quotient theorem, proving flatness, surjectivity, local finite
presentation and equality of the full kernel subgroup functor with
`SubgroupFunctor.range i`.

`homogeneousQuotientGroupScheme_etale` uses the open immersion supplied by
`hi`, the smooth surjectivity supplied by `D`, and the all-test coset
condition `D.fibers`. The published
`etale_of_open_subgroup_quotient` proves étaleness of the quotient over
`S`. The descended group has the same underlying scheme over `S` as `D`,
so the final existential theorem
`exists_etale_fppfQuotient_of_homogeneousQuotient` also keeps
`D.separated` and `D.quasiCompact`.

There is no quasi-compactness, separatedness or affineness premise on the
ambient group `G` in this construction. The necessary separatedness and
quasi-compactness of the quotient and projection are fields of `D`.
Neither existence of `D` nor closedness of `i` is proved or assumed
implicitly. This module assembles existing published constructions; it
uses no additional literature result or mathematical assumption.
