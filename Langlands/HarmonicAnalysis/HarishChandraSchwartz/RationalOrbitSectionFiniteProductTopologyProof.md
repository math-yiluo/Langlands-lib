# Finite-product topology comparison for rational orbit sections

`rationalOrbitSectionFiniteProductTopologyStatement_holds` proves
`RationalOrbitSectionFiniteProductTopologyStatement` by specializing
`orbitSectionFiniteProductTopologyStatement_holds` from the published
`OrbitSectionFiniteProductTopologyProof` module. All three declarations are
in `Langlands.HarishChandraSchwartz`.

The specialization uses the standard parabolic and its Levi and unipotent
subgroups in the locally compact nonarchimedean group `G(F)`. It applies
`isSemidirectDecomposition_standard`, the closedness results for the parabolic
and unipotent subgroup, and `continuous_projection_standard`.
`exists_standardParabolicPoints_rootSet_mul` derives the standard-parabolic
covering from the minimal Iwasawa pair. The norm characters have their
published continuity proofs, torus coordinates come from
`leviRationalUnitaryCoordinates`, and `compactOpenCofinal_standardLevi`
supplies compact-open cofinality in the standard Levi subgroup of `G(F)`.
The finite torus coordinate index is `Fin` of the standard Levi's
`rationalImageRank`.

For each open `H ≤ K`, the finiteness witness comes from
`finiteDimensional_rationalOrbitSectionFixedCoefficients`. The generic
level equality is definitionally the rational level equality for each
finite basis. For the total equality, the two families of finiteness
witnesses are interchangeable by proof irrelevance. The existing space
`rationalInducedOrbitSectionSpace` is definitionally the specialized
generic section space.

The comparison implements the topology of the smooth self-twist covariant
sections in Waldspurger, *La formule de Plancherel pour les groupes
p-adiques*, VI.1 and VI.3, printed pp. 295–296 and 301. The level equality
gives the actual sections the subspace topology from their finite coordinates.
The total equality gives them the corresponding locally convex inductive-limit
topology. The field has arbitrary characteristic, and the field, representation
carrier and finite coefficient basis index have independent universes.
[Waldspurger, 2003](https://doi.org/10.1017/S1474748003000082)
