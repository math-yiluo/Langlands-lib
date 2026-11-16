# Finite volume of the restriction split-centre adelic quotient

Author: Worker 679.

The theorem
`Langlands.Global.RestrictionSplitCentre.connectedReductiveQuotientFiniteVolume`
proves exactly the published proposition
`Langlands.Global.RestrictionSplitCentre.ConnectedReductiveQuotientFiniteVolumeStatement`.
It has no additional premises.

For every number field `F : Type`, every group scheme `G` over `Spec F` with
`IsAffine G.X.left`, `LocallyOfFiniteType G.X.hom` and
`IsConnectedReductive G`, every commutative group scheme `S` over `ℚ`, and every
`j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G` satisfying `IsSplitComponent j`,
the conclusion is
`IsFiniteMeasure (quotientHaarMeasure F G S j)`.
The quotient is the published left quotient
`[G] = A_G G(F) \ G(𝔸_F)`, where the positive real points of the chosen split
component give `A_G`.

## Implemented proof

The proof composes two published theorems:

1. `Langlands.Global.AdelicGroupPoints.connectedReductiveFiniteVolume`,
   imported from `Langlands.Global.AdelicFiniteVolumeProof`, proves
   `ConnectedReductiveFiniteVolumeStatement`. It gives finite measure for
   `normOneRationalQuotientHaarMeasure F G` on `G(F) \ G(𝔸_F)¹`.
   This theorem is used at universe zero, as required by the target's
   `F : Type`.
2. `connectedReductiveQuotientFiniteVolumeStatement_of_normOne`, imported
   from the target module
   `Langlands.Global.AdelicRestrictionSplitCentreFiniteVolumeStatement`,
   converts that result into the exact target.

The second theorem uses
`quotientHaarMeasure_isFiniteMeasure_iff`. By definition,
`quotientHaarMeasure F G S j` is the pushforward of the norm-one quotient
measure along the measurable map `normOneToQuotient`, induced by inclusion of
representatives. Its total mass equals the original measure's total mass:
the preimage of the entire target is the entire source. The published
norm-one finite-volume theorem therefore supplies the required finiteness.
This total-mass argument does not use splitness of `j`; the closing theorem
retains the precise reductivity and split-component hypotheses of the
published target.

All mathematical inputs are imported Library proofs. This module adds the
unconditional closing theorem and does not change the target or its measure
normalization.

## Source and provenance

This is the finite-volume consequence of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), §2.6:
(2.20), printed p.68 (PDF p.85), defines `A_G`; (2.21), printed p.69
(PDF p.86), defines `[G]`; (2.22) and its following paragraph identify the
norm-one quotient with `[G]` for reductive groups over number fields.
Theorem 2.6.3 on printed p.69 gives finite volume of the norm-one quotient
for smooth connected groups. Thus finite volume of `[G]` is a derived
consequence, rather than a separate theorem stated there. The implemented
proof uses the Library's pushforward measure and its published total-mass
lemma to express this consequence.

Registered source: `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
§2.6, (2.20)–(2.22) and Theorem 2.6.3, printed pp.68–69.
The registered October 2026 author errata,
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
contain no Chapter 2 entry.
