# Continuous descent through a compact factor

This internal topological helper works in any topological group. Multiplication
from a closed subgroup times a compact subgroup is a closed map: embed the
closed subgroup into the group, apply the homeomorphism sending `(g,k)` to
`(gk,k)`, then project along the compact factor.

When multiplication is surjective, it is therefore a quotient map. A continuous
function on the closed subgroup that agrees whenever two elements differ on
the right by an element of the compact subgroup descends to a continuous
function on the whole group. The construction chooses one factorization at each
point. The compatibility assumption makes its value independent of this choice,
and continuity follows from the quotient-map criterion.
