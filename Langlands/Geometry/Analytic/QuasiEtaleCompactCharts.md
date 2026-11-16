# Compact quasi-étale chart objects

This internal construction supports the compact quasi-étale comparison. It
derives quasi-étale chart composites from the published local factorization
condition, without assuming general quasi-étale composition or base change.

`domainPreimageIso` restricts a localized isomorphism to the literal inverse
image of a target analytic domain. The inverse image condition for the inverse
map follows from the isomorphism identity. The published domain restriction
isomorphism supplies the actual inverse arrows and inclusion triangle.

For an étale arrow, choose the strong representative and its arrow-category
isomorphism from the definition of `etale`. Pull the domain back through its
source isomorphism. Saturate that domain and compose its inclusion with the
étale strong representative. Each source chart of the new saturation is an
affinoid domain of the original source, by the proved saturation-chart domain
inclusion theorem. Taking that original source as the intervening étale space
proves the quasi-étale local condition. The restricted source isomorphism and
the original target isomorphism identify the constructed arrow with the
required domain inclusion followed by the étale map.

`quasiEtale_comp_of_isAffinoidDomainEmbedding_of_etale` also allows a supplied
source isomorphism in the affinoid-domain embedding. It uses the published
arrow-isomorphism invariance of `quasiEtale`. Chart domains are compact and
Hausdorff by the published compactness theorem for chart ranges.

Consequently, every chart selected by the local quasi-étale condition is itself
a quasi-étale object over the target. Its defining triangle expresses its
structure map as a supplied affinoid-domain embedding followed by an étale
arrow. The local finite families retain their original neighborhood-union
condition.

The general domain transport construction permits separate space and chart
universes. The quasi-étale constructions use the equal space and chart-index
universe required by the existing site. All fields remain complete
ultrametric normed fields. No new original-literature attribution or unproved
Library proposition is used. Finite global chart covers, actual finite nerve
presentations, general quasi-étale stability, and the cohomological comparison
remain separate obligations in this draft.
