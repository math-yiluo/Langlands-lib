# Actual quasi-split lifts from multipliable unitary depths

This internal reduction isolates the remaining existence input for
the published `QuasiSplitIndivisibleDerivativeLiftsStatement`.

For any connected reductive group and actual maximal split torus, the published
`rootRankOneFactorization` theorem supplies opposite factor pairs. Smoothness
comes from connected reductivity and splitness from the maximal split torus
hypothesis. `no_quadruple_root_of_oppositePairs` then excludes quadruple
relative roots by the integral root-coroot pairing. The conditional lift
theorem in `UnitaryIndivisibleAffineLifts` therefore needs no separate
no-quadruple-root premise on these actual groups.

`QuasiSplitMultipliableUnitaryTowerDepthsStatement` has the same field,
surjective integer valuation, henselian valuation ring, actual quasi-split
group, prescribed maximal split torus, arbitrary apartment, actual centralizer
and full centralizer compatibility scope as the published lift target. Its
conclusion asks for unitary coordinates only for relative roots whose double
is a relative root. For each such root it asks for a point of the supplied
apartment where all ordinary coordinate depths equal the original
base-normalized `SU3Root.towerDepth`. Different roots may use different points.
There is no requirement of a common origin or of separately supplied
negative-root depths.

The final theorem applies this existence premise to the actual inputs of the
published target and then applies the connected-reductive lift theorem above.
It proves the exact target proposition conditionally on this existence
statement at every universe parameter `u`. All full derivatives, including
multipliable ones, and all compatible apartments are retained. There is no
restriction on field characteristic, residue characteristic or residue
perfection.

This is an internal composition of published actual rank-one factorization
with the coordinate jump and finite-tower arithmetic development. It does
not establish the remaining algebraic coordinate and exact depth existence
premise. It uses no local anisotropic classification or local Kneser–Tits
input.
