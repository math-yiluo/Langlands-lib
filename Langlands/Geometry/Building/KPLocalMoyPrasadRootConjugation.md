# Actual torus-depth coordinates for K-level opposite conjugation

This internal proof module adapts `MoyPrasadRankOne` and the final portion of
`MoyPrasadRootConjugation` to the published groups over the maximal unramified
extension. Its explicit `LocalTorusCommutatorFriendly` hypothesis is precisely
the first clause of `QuasiSplitLocalTorusFiltrationStatement` at the given
building data and torus; the module does not assert that clause unconditionally.
No apartment axiom is assumed.

`LocalTorusCommutatorFriendly` and `exists_rankOne_depth_factorization` are
imported from the published `KPLocalMoyPrasadRankOne`. The factorization retains
the two root depths and puts its actual centralizer factor at their sum depth,
conditional on that commutator clause. This module uses those declarations
without defining them again.

`rootConjugationMoyPrasadCoordinates` compares this exchange with the root
coordinate bound proved in `IntegerRootConjugation`. Injectivity of the actual
opposite-root/centralizer/root product identifies the positive coordinate with
the retained constant-depth root block. The order-one unit required by that
integer-valued proof is the published `MaximalUnramified.exists_order_eq_one`.
Finally, `conjugate_opposite_mem_moyPrasad` includes the negative root coordinate,
the actual torus factor and the positive block into the defining group. This
handles exactly opposite directions at positive depth. Proportional doubled
opposite directions and the unconditional full target remain separate work.

The provenance is an adaptation of the cited Library proofs to
`IntegerValuationBuildingData` and the actual D1 torus filtration. These are
internal steps toward `LocalMoyPrasadGroupPropertiesStatement`, not an independent
claim to the full statement.
