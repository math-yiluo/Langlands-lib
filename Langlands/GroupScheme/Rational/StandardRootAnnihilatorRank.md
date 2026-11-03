# Standard-root annihilator rank from the relative root system

Author: Worker 1322.

This internal assembly connects the existing relative-root-system proposition
with the full first conjunct of `StandardLeviCentralDirectionsStatement`.
It retains the original actual character lattice, real cocharacter space,
simple-root selection and split-torus rank.

`RelativeRootSystemImpliesStandardRootAnnihilatorRankStatement` is the
proposition asserting the full implication at arbitrary universe. The final
theorem `relativeRootSystemImpliesStandardRootAnnihilatorRankStatement` proves
this proposition by the conditional reduction described below.

For an actual affine group scheme and a monic split torus map,
`HasRelativeRootSystem.standardRootAnnihilatorRank` assumes the existing
`HasRelativeRootSystem i` realization. It obtains finiteness of any selected
simple-root subset from the finite relative-root system, and rational
independence by restricting the published simple-root independence theorem.
The real cocharacter dimension equals the split-torus rank by the finite real
torus-space theorem. The annihilator is a subspace of a finite-dimensional
space, and the independent-character rank-nullity theorem gives the required
codimension formula.

The global theorem
`standardRootAnnihilatorRankStatement_of_relativeRootSystemStatement` specializes
this construction using the connected reductive group and maximal split torus
in the existing unrestricted statements. Its hypothesis is the full
`RelativeRootSystemStatement`; its conclusion is the full
`StandardRootAnnihilatorRankStatement`, at the same arbitrary universe.

The provenance is derived from the cited Library constructions and their proved
linear-algebra laws, with no external source invoked. This is a conditional
reduction: it does not prove `RelativeRootSystemStatement`, unrestricted
simple-root independence, the standard-Levi geometric realization, or the
full `StandardLeviCentralDirectionsStatement`.
