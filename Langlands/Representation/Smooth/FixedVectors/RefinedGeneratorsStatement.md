# Refined common fixed generators

Worker 1210, in coordination with Worker 189.

This internal statement unit refines the published
`Langlands.CommonFixedGeneratorsStatement`. It records two elementary choices
of a subgroup fixing a finite generating family. The declarations are
proposition definitions; this unit supplies no proofs.

`CommonCompactOpenNormalGeneratorsStatement` quantifies independently over a
commutative coefficient ring `R`, a nonarchimedean topological group `G`, a
module carrier `V`, and a representation `ρ`. Smoothness and finite generation
of the actual `MonoidAlgebra R G` module are assumed. For every supplied compact
open subgroup `K₀` and every identity neighborhood `U`, it asserts a finite
family generating that actual module and a compact open subgroup `K` contained
in `U` and in `K₀`. The subgroup `K`, viewed as a subgroup of the same `K₀`,
is normal. Every chosen generator is fixed by `K`. For every subgroup `L`
contained in `K`, any subrepresentation containing `fixedVectors ρ L` is the
whole representation. No nonzero-carrier or positive-family-size premise is
imposed.

The internal derivation is to start from the published common generators and
their open stabilizer, intersect with a sufficiently small open subgroup,
and pull back to the compact group `K₀`. Mathlib's
`IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`
provides an open normal subgroup there. Its image in `G` is open, closed,
contained in `K₀`, and therefore compact. Compactness of the supplied `K₀`
is sufficient; no separate local compactness hypothesis is required.

`CommonBasisFixedGeneratorsStatement` instead takes a supplied set `B` of
subgroups whose underlying sets form an identity-neighborhood basis. It
asserts a member `K ∈ B` contained in any prescribed identity neighborhood,
together with a finite actual group-algebra generating family fixed by `K`
and the same generation property for all smaller subgroups. This assertion
requires only a group with a topology. The basis property chooses `K` inside
the intersection of the prescribed neighborhood and the common open
stabilizer. Consequently any separately supplied properties of members of
`B` remain available for this chosen member.

`RefinedFixedGeneratorsStatement` is the conjunction of these two targets,
with independent coefficient, group, and carrier universes. Their provenance
is the published common-generator result and the topological and filter-basis
arguments just described, rather than a new assertion attributed to the
literature. The motivating fixed-generator step of Renard VI.6.3 is documented
in [LengthCriterionStatement.md](LengthCriterionStatement.md).

The compact-open normal assertion does not provide Iwahori decompositions or
contraction data. The basis assertion assumes its actual basis and proves no
structural existence result. The unrestricted rational-point Howe target,
its converse, the VI.6.3 intermediate assertions, and the stronger bound for
the specially chosen subgroup retain their separate obligations.
