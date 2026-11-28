# Gluing the translates

`Glue.core` uses the overlaps and the transition cocycle to supply gluing
data for a family `τ : ι → Translation m`. Each chart is a copy of `Y`.
The gluing API gives open chart immersions which cover the result and identifies
their intersections with the specified overlaps. In particular, two morphisms
into charts that agree in the glued scheme factor through the appropriate
transition. The structure maps to `S` agree on the transitions and descend,
and smoothness follows from the open cover.

This construction uses the same closed-graph overlaps as the gluing of
`X` and `X(a)` in BLR, *Néron Models*, §5.3, p. 122, for one chart family.
