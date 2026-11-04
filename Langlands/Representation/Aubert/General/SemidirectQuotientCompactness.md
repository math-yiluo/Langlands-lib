# Compact quotients inside an actual semidirect Levi

This internal supporting construction transfers compact representatives from an
ambient group to its actual Levi subgroup. It applies to any group `G` with a
topology and an actual `IsSemidirectDecomposition P M U`. No reductive group,
root labeling, or representation is required.

`leviCosetRepresentatives h C` is the image under the actual Levi projection
`P → M` of the inverse image of `C ⊆ G` under the inclusion `P → G`.
Thus it first intersects the ambient representatives with `P`, and then
projects to `M`. If `P` is closed, its inclusion is a closed embedding;
the inverse image of a compact set is compact. A continuous projection then
proves `isCompact_leviCosetRepresentatives`.

Suppose `U ≤ Q ≤ P` and every `g ∈ G` is `q * c` for some `q ∈ Q` and
`c ∈ C`. For `m ∈ M`, choose such a factorization. Both `q` and `m` lie in
`P`, so `c = q⁻¹ * m` also lies in `P`. Apply the projection to the
factorization. The published `projection_mem_of_radical_le` puts the
projection of `q` in the literal subgroup `Q.subgroupOf M`; the projection
of `c` belongs to `leviCosetRepresentatives h C`. The projection fixes `m`,
so this is the required factorization in `M`. This proves
`leviCosetRepresentatives_cover`.

`hasCompactCosetCover_subgroupOf_levi` combines these two facts. For a weakly
locally compact topological group,
`compactSpace_leftQuotient_subgroupOf_levi` first obtains a compact coset cover
from compactness of `Q \ G`, then obtains a compact coset cover inside `M`,
and finally concludes that `(Q.subgroupOf M) \ M` is compact. The cosets use
the published `Langlands.Induction.LeftQuotient`, whose representatives are
`Q * g`. No normality of `Q` is assumed.

The declaration-level dependencies are the projection, its homomorphism law
and `projection_levi` in `Parabolic`, `projection_mem_of_radical_le` in
`RationalInductionStagesGeometry`, and the compact-cover equivalence in
`RationalIwasawaCartan`. The compactness argument also uses Mathlib's closed
subtype embedding, compact inverse images under closed embeddings, and
compact continuous images. This is an internal deduction from those published
results. It uses no classification, character independence, geometric lemma,
adjointness, or cuspidal-support theorem.

This unit leaves compactness of the ambient quotient explicit. In the intended
standard-family application, `Q` is a finer parabolic and `P` the coarse
parabolic; the quotient in the conclusion is the literal quotient inside the
coarse Levi. The result neither proves ambient parabolic quotient compactness
nor proves inside-Levi cuspidal-series existence or the full support-category
Jacquet-vanishing proposition.
