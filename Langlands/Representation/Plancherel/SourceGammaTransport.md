# Exact transport of source-normalized Haar measures and gamma

This is a derived comparison for Waldspurger's common-compact normalization
in I.1, printed p.240 / PDF p.6, immediately before formulas (2) and Remark
(3). The registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The comparison is internal; the source does not state this transport theorem
as a separate numbered result.

The two ambient topological groups have independent arbitrary universes and
their Borel measurable spaces. A continuous group isomorphism `e` carries
the original closed subgroup, parabolic, opposite subgroup and chosen compact
open to the corresponding target objects, as specified by membership
equivalences. Only the target ambient group needs a local compactness
assumption in the normalized measure comparisons. No splitness, characteristic,
representation-carrier or countability restriction is imposed.

`sourceCompactImage e K` uses the existing open-subgroup inverse-image
constructor with `e.symm`. It is the image of `K` under `e`. Membership
at `e g` is exactly membership of `g` in `K`, and compactness follows
from the inverse homeomorphism.

`measurePreserving_sourceSubgroupHaar` uses the existing
`QuotientIntegration.subgroupContinuousMulEquiv` on the corresponding literal
subgroups. Pushforward of the original intrinsic normalized Haar is a
regular Haar measure on the target subgroup. Its mass on the target compact
intersection is one, because the inverse image is precisely the original
compact intersection. The published regular Haar uniqueness theorem therefore
identifies the pushforward with the existing target normalization exactly.
Neither measure is obtained by restricting an ambient Haar measure.

`openCellConstant_eq_of_transport` also applies to supplied subgroup measures
whenever the restricted group isomorphisms preserve them. Change of variables
in the two lower integrals carries the indicator of the target compact at
`e(p) e(v)⁻¹` to the indicator of the original compact at `p v⁻¹`.
The measurable-embedding change-of-variables theorem avoids a separate
integrability or measurability premise on the intermediate integral.

`compactNormalizedSourceGamma_eq_of_transport` combines these two results
for the existing common-compact gamma, preserving its precise scale. It
needs no semidirect presentation, chosen Iwasawa components, Haar measure on
the ambient group, open-cell embedding, conullness or convergence assumption.
It does not prove independence between arbitrary parabolics with a fixed
Levi. The source's root-index factorization, special-compact realization,
gamma finiteness and positivity, and the Plancherel conclusions remain
separate obligations.
