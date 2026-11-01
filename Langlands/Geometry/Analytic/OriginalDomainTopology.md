# Quasinet coverings of fixed-original-chart domains

Fix an actual indexed affinoid atlas `a` over a complete ultrametric normed
field `K`, on a topological space `X`. The coefficient, point and chart-index
universes remain independent. The published type `OriginalChartDomain a`
consists of actual subsets with the finite relative neighborhood condition
for contained charts of `a`. It carries the subset order, literal
intersections, and constructed subspace affinoid atlases. Its category has
one arrow for each inclusion. The published `originalDomainFunctor` sends
these arrows to actual chosen bounded atlas inclusions.

For a sieve `R` on `S`, `sieveFamily R` consists of the underlying subsets of
the source domains of its arrows. Every such subset lies in `S`, and
`sieveFamily_mono` proves monotonicity. `IsCovering R` means that, for each
`x ∈ S`, there is a finite family of these source subsets, all containing
`x`, whose union is a neighborhood of `x` relative to `S`.
`isCovering_iff_isQuasinet` identifies this condition with the quasinet
condition on the actual target subspace through `restrictedFamily`.

`quasinetTopology` constructs a Mathlib `GrothendieckTopology` on this
category. The maximal sieve covers using the single domain `S`.
`IsCovering.pullback` constructs base change by intersecting each of the
finitely many witnessing domains with the source domain `T`. These
intersections are objects of the same category. Sieve downward closure
puts their inclusion arrows in the pulled back sieve, and the published
intersection refinement theorem supplies the relative neighborhood.
`IsCovering.transitive` uses the published `LocallyRefines.trans`: it
substitutes finite witnesses in each member of a covering sieve and
combines them into a finite relative neighborhood. The composite inclusion
arrows belong to the target sieve. `IsCovering.mono` and
`mem_quasinetTopology` expose monotonicity and the covering predicate.

For an arbitrarily indexed family of inclusions `f i : D i ⟶ S`,
`ofArrows_mem_iff_locallyRefines` characterizes membership of its generated
sieve by the same finite relative neighborhood condition on the actual
family of subsets `D i`. The forward implication takes finite sieve
witnesses and chooses a generating domain containing each witness. The
finite family of chosen domains still contains the point, lies in `S`,
and its union contains the original relative neighborhood. The reverse
implication, also given by `ofArrows_mem_of_locallyRefines`, inserts the
generating arrows in their generated sieve.
`ofArrows_mem_iff_isQuasinet` translates this exact criterion to a quasinet
on the target subspace. Empty index types are allowed.

`ofArrows_originalCharts_mem` proves that all original charts contained in
`S` form a covering family. It converts the domain's finite neighborhood
witnesses to contained chart indices. `IsCovering.exists_mem` derives
point coverage by actual sieve domains. Finally,
`bot_mem_quasinetTopology_iff` proves that the empty sieve covers precisely
the empty domain: point coverage rules out any point in a domain covered
by the empty sieve, and the condition on the empty domain is vacuous.

The source is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), section 1.1, printed p.13 / PDF p.10, for quasinets and
induced subspaces; Definition 1.3.1, printed p.23 / PDF p.20, for analytic
domains; and the G-topology paragraph in section 1.3, printed p.25 /
PDF p.22, for coverings by quasinet families of domains. Registered source:
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

This is a derived construction of that covering rule on the published
fixed-original-chart domain category. The finite intersection and
refinement proofs establish its topology axioms directly. It does not
identify this restricted category with all analytic domains, construct a
maximal atlas, prove a representable or structural presheaf is a sheaf,
or construct the full analytic or étale site.
