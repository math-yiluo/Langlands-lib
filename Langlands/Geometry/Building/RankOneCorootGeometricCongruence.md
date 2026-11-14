# Geometric character congruence for transported rank-one coroot points

`CorootComponentCongruenceProperty B hZ a T f` is the factorization and
all-geometric-character clause of `KPLocalCorootComponentStatement` for
a specified root character, commutative source group scheme, and
morphism into the actual centralizer torus. It retains the nontriviality
and positive finite depth hypotheses of that target. The definition does
not assert that its source is a torus or that suitable coordinates exist.

For supplied `ValuedSL2RootCoordinates`, `corootMorphism` views the
supplied scheme coroot in the category of commutative group schemes.
The theorem `corootComponentCongruenceProperty` proves the property for
this morphism and the actual finite separable Weil restriction of the
multiplicative group. It first applies
`exists_corootPoint_of_factorization` to identify the supplied
centralizer component and find a unit whose normalized difference value
equals the positive depth sum. The rational source point is the inverse
image of that unit under `WeilGm.rationalUnitsEquiv`.
`MaximalUnramified.weilGm_geometricCharacter_bound` then gives the
required inequality for every character over `SeparableClosure F`.

The unitary namespace gives the same construction and argument.
`corootComponentCongruenceProperty` uses the ordinary-root lower bound,
and `double_corootComponentCongruenceProperty` uses the exact
doubled-root value. In both cases the rational source and geometric
valuation are exactly those in the target, with the original local
field normalization.

These are internal consequences of `RankOneCorootTransport` and
`KPLocalWeilRestrictionCongruence`. They use supplied coordinate records
and do not assume a named coordinate-existence proposition. They do not
prove that records exist for an arbitrary root, assert inducedness of
the source torus, or establish the final unconditional coroot target.
