# Fibrewise affineness from universal torus families and the Weyl criterion

This internal assembly reduces the exact proposition
`Langlands.GroupScheme.ReductiveFiberAffinenessStatement.{u}` to two explicit
mathematical inputs, over every base scheme and in every universe:

- existence of smooth universal families of closed relative-torus subgroups for
  smooth separated quasi-compact group schemes with affine actual residue fibres;
- `SelfCentralizingTorusWeylAffinenessStatement.{u}`, the structural existence and
  affineness criterion for the normalizer and Weyl quotient of a supplied closed
  self-centralizing fibrewise maximal relative torus.

Neither input is proved by this module. The first has the exact intended type of
`TorusSubgroupModuli.SmoothAffineFiberTorusSubgroupRepresentabilityStatement`;
it is written out here, so that this module does not import that statement. The Weyl
criterion is an existing Library proposition. In particular, this module is
a conditional reduction and does not prove the target unconditionally.

`SelfCentralizingWeyl.finiteWeylModelOfCriterion` constructs the actual
`FiniteWeylModel t` from the Weyl criterion and a supplied closed
self-centralizing fibrewise maximal relative torus in a smooth separated
quasi-compact group with connected reductive actual residue fibres. It supplies
the actual smooth closed normalizer, finite etale Weyl quotient, flat
surjective locally finitely presented quotient projection, all-test kernel
identity and ambient relative affineness.

The construction applies `SelfCentralizingWeyl.valuationFiniteWeylModel` and
discharges its valuation hypothesis with
`Langlands.AlgebraicGeometry.isAffineHom_etale_algClosedValuation`. That imported
theorem proves affineness of quasi-compact separated etale schemes over valuation
subrings of algebraically closed fields. It is a proved theorem here, not an
additional supplied input. Its proof uses split standard-etale local
presentations, local isomorphisms over valuation spectra and finite local
affine charts. No Noetherian, rank, discreteness or henselian hypothesis enters
this application.

`reductiveFiberAffineness_of_torusFamilies_of_weylCriterion` applies the imported
etale torus-family reduction. On each actual etale neighbourhood, the preceding
constructor supplies ambient affineness through its `group_affine` field. The
imported reduction descends this affineness and produces exactly the original
proposition, with the two remaining inputs explicit. Connected reductivity is
used on the actual residue fibres; global affineness is a conclusion.

The provenance is internal composition of the imported constructions and proved
valuation affineness.
No external-source result is newly transcribed by this module.
