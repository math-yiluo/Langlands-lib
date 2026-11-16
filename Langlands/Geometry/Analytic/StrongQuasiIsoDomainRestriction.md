# Full quasi-isomorphisms on actual inverse-image domains

This internal construction works for saturated atlas presentations over a
complete ultrametric normed field, with independent space and chart
universes. For a full strong quasi-isomorphism `s : A → B` and an actual
analytic domain `D` of `B`, `QuasiIsoDomainRestriction.preimageDomain` is the
literal subset `s⁻¹(D)` with the proved analytic-domain structure.

Every original chart of `A` retained in this inverse-image domain has an
entire image which is an original chart of `B`. The existing direct-image
construction for full quasi-isomorphisms, applied to the whole local
source domain, supplies this chart. Its range lies in `D`, so these charts
give the target witnesses needed by the existing full domain restriction.
`QuasiIsoDomainRestriction.map` is the resulting strong map to `B.domain D`.
Its bounded pullbacks are the original pullbacks of `s`.

The restricted map is again a full quasi-isomorphism. Its point map is the
restriction of the original homeomorphism onto the inverse-image domain,
and its local domain representation is inherited from `s`. Surjectivity
of that homeomorphism gives the exact image `D`, as required by the
existing restriction theorem.

The general lemma `restrictDomains_comp_domainInclusion` proves that full
strong domain restriction commutes with the two actual inclusions. The
proof compares complete bounded pullbacks at each retained source chart
and a containing target chart. The source and target inclusion formulas
both give the original ambient pullback. The specialized theorem
`QuasiIsoDomainRestriction.map_comp_domainInclusion` records this square.
No equality of analytic arrows is inferred from pointwise equality.

These are derived constructions from the proved inverse-image domain,
direct-image chart and full strong restriction APIs. They provide a
denominator for restricting right fractions. Restriction of the
near-identity relation and continuity of restricted actions require
further arguments.
