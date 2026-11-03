# Opposite factor-pair existence from the existing geometric targets

This module constructs an actual ordered opposite factor pair conditional
on the two existing geometric propositions `RationalBruhatStatement` and
`KernelCentralizerComponentReductiveStatement`. These propositions remain
explicit inputs and are not proved here. The construction applies over
arbitrary fields and universes to every point of the intrinsic subgroup
for any nonzero character of an actual maximal split torus in a connected
reductive group. Root occurrence and nonidentity of the point are not
required for this existence construction.

The provenance is internal, through the existing full-kernel component
and rational Bruhat interfaces. The action lemmas extend the published
positive-power result in [`PositivePowers`](../Dynamic/PositivePowers.md)
using the actual semidirect product comparison in
[`SemidirectDynamic`](../AutomorphicAction/SemidirectDynamic.md).
The component argument uses
[`RootKernelIdentityRoot`](RootKernelIdentityRoot.md) and
[`RootFactorPairTransport`](RootFactorPairTransport.md), and the passage
from parabolic to unipotent double cosets uses
[`BruhatContractionReduction`](BruhatContractionReduction.md).

`fixedSubgroup_restrict_of_fpqc` proves equality of the all-test fixed
subgroups before and after an fpqc restriction. To prove the nontrivial
inclusion, check the required point equality after locally lifting the
acting point; apply the restricted fixed-point law on that refinement.
The reverse inclusion is direct restriction. This proof preserves
nonreduced test schemes and acting points that have no global lift.

`unipotent_restrict_positive_power` uses the actual semidirect product of
the original affine group by the acting Gm. The original action's
identity-limit subgroup is the preimage of the ambient dynamic unipotent
subgroup under the normal-factor inclusion. Positive scaling preserves
that ambient dynamic subgroup by the published theorem, hence preserves
the original action's identity-limit subgroup as well.

For a torus action that actually descends through a nonzero character
`a`, restriction along a cocharacter `ν` is the pairing power
`t ↦ t^⟨a,ν⟩` of the descended Gm-action. For a positive pairing,
`dynamicUnipotent_eq_subgroup_of_descendedAction` therefore identifies
the actual dynamic subgroup with the intrinsic `a` subgroup. For a
nonzero pairing, the pairing power is fpqc; the fixed-subgroup result
identifies its dynamic centralizer with the full torus centralizer.
The corresponding two component lemmas apply this to the actual
descended action of the full-kernel identity component. No root-system,
finite-Weyl-group, or generic-centralizer proposition is assumed.

`exists_genericCocharacter_pairing_pos` avoids the finite union of the
actual root hyperplanes and one additional specified character
hyperplane. If necessary, negate the resulting integral cocharacter so
that its pairing with the specified nonzero character is positive.
This uses actual root-support finiteness, not a root-system structure.

To construct the factor pair, first handle the identity point with the
identity pair. For a nonidentity point, take a smooth closed representative
of the full character-kernel centralizer using
[`KernelCentralizerStructureProof`](KernelCentralizerStructureProof.md).
The component-reductivity input makes its actual identity component
connected reductive. The original maximal split torus remains maximal
split there. Choose a generic cocharacter pairing positively with `-a`.
The rational Bruhat input gives parabolic double-coset covering in this
component. The proved full-torus centralizer identity and the published
pointwise Levi factorizations convert it to a covering by
`U(-a)(k) n U(-a)(k)` with `n` in the actual normalizer. Negation invariance
of the full kernel identifies `U(-a)` using the same component and torus
inclusion as for `a`.

For a component point written `y = u * n * v`, the ordered pair
`(u⁻¹,v⁻¹)` satisfies the original `IsOppositeFactorPair` predicate:
both factors belong to the intrinsic opposite subgroup, and their
product with `y` is exactly `n`. The universal existence equivalence in
`RootFactorPairTransport` carries this result to the original ambient
root point. `oppositeFactorPairOfBruhatAndComponentReductivity` selects
the actual ordered pair together with that predicate.

Only the covering half of rational Bruhat is used. The proof does not
use rational Bruhat separation, a relative root system, root reducedness,
or a generic-centralizer theorem. It imposes no field, characteristic,
primitivity, or smooth-kernel restriction. The two unproved geometric
inputs remain indispensable premises of this auxiliary construction.
Consequently this module does not prove unconditional pair existence
or `RootRankOneFactorizationStatement`.
