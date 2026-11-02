# Matrix coefficients modulo a prescribed central subgroup

Author: Worker 200.

Waldspurger III.1, printed p.263 (PDF p.29), defines square-integrability
for an admissible representation with a unitary central character by requiring
all matrix coefficients to be square-integrable on `A_G \ G`. Here `A_G` is
the maximal split torus in the center from I.1. Source ID:
`waldspurger-2003-plancherel`; SHA256:
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

This module constructs the coefficient functions and predicate for a group `G`,
a specified normal subgroup `A`, and a proof `hA : A ≤ Subgroup.center G`.
These are actual subgroups and quotient groups. The topological projection
`centralQuotientProjection A hA` maps the class of `g` modulo `A` to its class
modulo the full center. Its continuity is proved by the quotient topology.
`centralSubgroupCoefficientNorm` pulls the Library's actual descended absolute
matrix coefficient back along this map; evaluation on the class of `g` is exactly
`norm(matrixCoefficient ρ ℓ v g)`. The centrality assumption identifies left and
right cosets in the source convention.

`IsSquareIntegrableModCentralSubgroup A hA ρ μ` requires the Library's actual
admissibility predicate, a `UnitaryCentralCharacter ρ` of the full center, and
`MemLp` with exponent 2 for every smooth-dual functional and vector on the
actual quotient `G / A`, with the specified Haar measure `μ`. There is no
topology on the representation carrier. Group and carrier universes are
independent. The predicate requires a topological group and a measurable
quotient carrying a Haar measure; no rational-point instances are inferred.

Internal well-definedness adapters show independence of the central-character
witness, transport of coefficient norms and square-integrability through actual
equivariant linear equivalences, and preservation under norm-one open-kernel
character twists. They reuse the Library's `UnitaryCentralCharacter.ofEquiv`,
`coefficientNorm_ofEquiv`, `unitaryTwist`, and
`coefficientNorm_unitaryTwist`, as well as its smooth-dual twist equivalence and
admissibility preservation. They are direct quotient/coefficient comparisons,
not a proof of the exponent criterion or unitarity theorems in III.1.

For the Waldspurger specialization `A` must be the actual rational-point split
center with its inclusion and topology. This module makes that input explicit;
it does not construct a reductive framework or identify an arbitrary central
subgroup with that split center. It also does not prove equivalence with the
Library's full-center `IsSquareIntegrableModCenter`, whose quotient is generally
different. That comparison needs the actual compact central quotient, quotient
measure formulas and their `MemLp` comparison. Those remain separate obligations.
