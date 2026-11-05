# Bounds on Cartan pairings from vanishing proper Jacquet modules

This internal proof-support unit implements the finite-wall gap argument in
Renard VI.2.1, proof of (a) implies (b), printed p.139 / PDF p.145 of the 2026
edition. It bounds simple-root pairings on the nonzero set of an individual
coefficient. It does not assert compact restriction or finite-dimensionality.

`IsCartanLatticeModel.exists_coefficient_pairing_bound` assumes the published
`IsCartanLatticeModel`, a full Levi equal to the group, a linear map invariant
under an open subgroup, and a vector lying in each proper radical relation
space. It chooses one finite genuine relation witness per proper wall using
`Jacquet.relationContractionWitness`. The published
`IsCartanLatticeModel.eventually_wall_contraction` supplies successive integer
thresholds that absorb those witnesses. The finite-root gap argument gives a
wall with no pairing between two successive thresholds. If this wall is proper,
contraction annihilates the coefficient, contradicting nonvanishing. Otherwise
all pairings are below the final threshold. This includes an empty root set:
the conclusion then has no root coordinates to bound.

`coefficientPairingBound` chooses such an integer bound as data;
`coefficientPairingBound_spec` states its proved property. The coefficient map
may have values in any module over any commutative ring, independently of the
group, source and output universes. No smoothness of the source, admissibility,
irreducibility or finite-dimensionality is used; openness of the invariant
subgroup is the topological input.

The generic lattice model and its eventual wall contraction are imported from
`Langlands.Representation.Aubert.General.CartanLatticeContraction`. The finite
Jacquet witness construction and its correctness theorem come from
`Langlands.Representation.Aubert.General.CuspidalCoefficientVanishing`.
Actual reductive-group specialization, compact subgroup translates, joint
root/ambient-character detection and compact support remain separate steps.
