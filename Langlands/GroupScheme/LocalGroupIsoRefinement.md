# Refinement of local group isomorphisms and discrepancy

This internal construction works over every base scheme `S : Scheme.{u}`,
for arbitrary universe `u`. It uses the existing meanings of
`LocalGroupIso`, `AutomorphicAction`, and the actual natural `Cocycle`.
No covering, reductivity, or field hypothesis is required.

For `e : LocalGroupIso G H U` and any morphism `r : V → U` over `S`,
`LocalGroupIso.refine e r` assigns to a point `b : T → V` the supplied
multiplicative equivalence indexed by `b ≫ r`. The test scheme `T` and
its group points are unchanged. Associativity and the original
naturality law prove naturality for every relative test scheme and
morphism. `refine_toFun` records this evaluation formula.

`LocalGroupIso.IsIndependent.refine` preserves agreement of the local
maps, by evaluating their original agreement at the two composite
cover points. `LocalGroupIso.HasDiscrepancy.refine` similarly preserves
the actual discrepancy equation when both the local isomorphisms and
the cocycle are refined along `r`. It retains the same acting group,
action, and discrepancy orientation.

`Cocycle.refine_universal` identifies the universal overlap value of
the refined cocycle with the composite of `r × r : V ×_S V → U ×_S U`
and the original universal overlap value. This follows by specializing
cocycle naturality to the product refinement and its two projections.
Thus the refinement transports an actual morphism of schemes, as well
as its values on every test.

These are derived categorical adapters, proved directly from the
published definitions and their naturality laws. They do not construct
an initial local isomorphism, an initial cocycle, or a structural model.
