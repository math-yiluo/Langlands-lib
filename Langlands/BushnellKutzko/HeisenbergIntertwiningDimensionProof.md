# Dimension of the Heisenberg intertwining space

`heisenbergIntertwiningDimension` proves
`HeisenbergIntertwiningDimensionStatement` at independent field, stratum-space
and representation-space universes. This is Bushnell–Kutzko (1993),
Proposition (5.1.8), printed p. 160 (PDF p. 172).

`heisenbergRepresentation_of` gives the support formula
\(I_G(\eta) = J^1 B^\times J^1\) and the scalar restriction and degree
formulas of (5.1.1). Its inputs are `simpleCharacterPairing`,
`simpleCharacterIntertwining` and `simpleStratumGroupProperties`.
On the support, `heisenberg_intertwining_finrank_eq_one` in
`BetaExtensionTwist.Multiplicity` applies the intersection index comparison,
using the stratum lattice and group properties, to give dimension one.
Outside the support every intertwining map is zero by the definition of
self-intertwining, so the space has dimension zero.
