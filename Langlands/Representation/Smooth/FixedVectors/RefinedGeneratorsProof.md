# Proof of refined common fixed generators

Worker 1210, in coordination with Worker 189.

This proof unit targets the internal
`Langlands.RefinedFixedGeneratorsStatement`. Its two component proofs use the
published `Langlands.commonFixedGenerators`; the coefficient, group, and
carrier universes remain independent.

For `commonCompactOpenNormalGenerators`, obtain a finite actual group-algebra
generating family and its common open stabilizer `F`. Nonarchimedeanness gives
an open subgroup `J` contained in the prescribed identity neighborhood `U`.
Pull `F ∩ J` back to the supplied compact open subgroup `K₀`, obtaining a
clopen subgroup `H` of the compact topological group `K₀`. Mathlib's
`IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one` gives an
open normal subgroup `N` of `K₀` contained in `H`.

Map `N` into `G` along the actual inclusion of `K₀`. The image `K` is an open
subgroup because the inclusion of the open subset `K₀` is an open map.
It lies in `K₀`, in `F`, and in `J`. Every open subgroup of a topological
group is closed, so containment in the compact set `K₀` makes `K` compact.
Pulling this image back along the injective inclusion gives exactly `N`;
its normality is therefore the required normality of `K` inside the same
supplied `K₀`. Containment in `J` gives `K ⊆ U`, and containment in `F`
gives both the fixed-vector conclusion and the published generation property
for every subgroup contained in `K`.

For `commonBasisFixedGenerators`, again obtain the finite generating family
and open stabilizer `F`. The intersection `U ∩ F` is an identity
neighborhood. Apply `Filter.HasBasis.mem_iff` to the supplied basis to choose
`K ∈ B` contained in this intersection. Containment in `U` is the promised
smallness; containment in `F` transfers the fixed-vector and generation
properties. In particular the proof retains membership in the supplied `B`.

`refinedFixedGenerators` pairs these proofs. Neither proof assumes a nonzero
representation or a nonempty generating family. The statements and the
unrestricted rational-point Howe target are unchanged by this unit.
The provenance is the published common-generator proof and the explicit
Mathlib compact-group and filter-basis arguments above. This proves no
Iwahori decomposition, contraction property, structural basis existence, or
reductive subquotient detection. The full Howe implication, its converse,
the VI.6.3 intermediate assertions, and the stronger specially chosen
subgroup length bound remain separate obligations.
