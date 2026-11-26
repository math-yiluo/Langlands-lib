# Proof of affineness from connected reductive residue fibres

The theorem `Langlands.GroupScheme.reductiveFiberAffineness` proves the
proposition
[`ReductiveFiberAffinenessStatement.{u}`](FiberwiseAffinenessStatement.md) in
every universe, with its statement unchanged. For every scheme `S : Scheme.{u}`
and every group scheme `G` over `S` with `Smooth G.X.hom`, `IsSeparated G.X.hom`
and `QuasiCompact G.X.hom`, if every actual residue-field fibre
`RelativeIdentityComponent.residueFiber G s` is `IsConnectedReductive`, then
`IsAffineHom G.X.hom`. No hypothesis is placed on the base scheme.

## Proof

The proof is a single application of the conditional reduction
`reductiveFiberAffineness_of_torusFamilies_of_weylCriterion` of the module
[`ValuationTorusAffinenessReduction`](ValuationTorusAffinenessReduction.md).
That theorem concludes `ReductiveFiberAffinenessStatement.{u}` from two
hypotheses, and both are supplied by theorems of the Library.

1. **Universal torus families.** The first hypothesis asks, for every smooth
   separated quasi-compact group scheme with affine actual residue fibres, for
   a smooth parameter scheme over the base carrying a universal family of closed
   relative-torus subgroups. It is written out in the reduction with exactly the
   type of `TorusSubgroupModuli.SmoothAffineFiberTorusSubgroupRepresentabilityStatement.{u}`,
   so the theorem
   `TorusSubgroupModuli.smoothAffineFiberTorusSubgroupRepresentability` (module
   [`SmoothAffineFiberTorusSubgroupRepresentabilityProof`](../HomScheme/SmoothAffineFiberTorusSubgroupRepresentabilityProof.md))
   is passed as it stands.

2. **Weyl-quotient affineness criterion.** The second hypothesis is
   `SelfCentralizingTorusWeylAffinenessStatement.{u}`: for a closed fibrewise
   maximal relative torus that represents its own centralizer, the normalizer
   and an étale Weyl quotient exist, and the group is affine over the base
   exactly when the Weyl quotient is. It is supplied by the theorem
   `selfCentralizingTorusWeylAffineness` (module
   [`SelfCentralizingWeylAffinenessProof`](../Torus/SelfCentralizingWeylAffinenessProof.md)).

Inside the reduction, the torus families give, étale locally on the base, a
closed self-centralizing fibrewise maximal torus. The Weyl criterion, together
with the proved affineness of quasi-compact separated étale schemes over
valuation rings of algebraically closed fields, makes the Weyl quotient finite
and so the group affine on each such neighbourhood. Affineness then descends to
the original base. These steps are carried out in the imported modules; this
module adds no further argument.

## Sources

The statement is the everywhere-reductive consequence of M. Demazure and
A. Grothendieck (eds.), *Schémas en groupes* (SGA 3), Exposé XVI, Theorem 5.2(i)
(Gille–Polo recomposition, printed p.320, original pp.524–525); the source
locators and its use in Brian Conrad, *Reductive group schemes* (2014), proof of
Proposition 3.1.3, are recorded with the statement. The Library's proof follows
the source's outline through a maximal torus, its centralizer and the Weyl
quotient (SGA 3, Exposé XVI, Theorem 4.1), with the finiteness of the Weyl
quotient obtained from the valuative argument described in the reduction module
rather than from the source's reduction to discrete valuation rings.
