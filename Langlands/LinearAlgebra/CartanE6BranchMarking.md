# Relative-root restrictions with unmarked short arm in type E₆

With the short-arm vertex unmarked, an opposition-stable marking makes three
choices. It may mark both long-arm endpoints, both inner long-arm vertices,
and the central vertex independently. The star action either fixes all
vertices or exchanges the two long arms. The projection erases unmarked
coordinates and adds the coordinates in each marked star orbit at its
chosen representative. The signed list of projections includes zero.

`HasIntegralReflections` requires an integer pairing vector `f` for every
active coordinate `i` and every positive integer `m` for which `m eᵢ` is a
signed root projection. It requires `m * f i = 2` and closure of the signed
projection list under `c ↦ c − m (∑ⱼ cⱼ fⱼ) eᵢ`.

The reflection reverses the pivot coordinate in each fiber through another
marked orbit basis vector. The minimum and maximum coordinates in that
fiber determine the pairing. For each marking of an inner long-arm vertex
or the central vertex, the verified root list contradicts either integrality
or closure under the forced reflection. For instance, marking only the
center gives a projected root of multiplicity three, which violates the
normalization. Thus the only possible marks under this condition are the
two long-arm endpoints.

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (Academic Press,
1994), §6.8, printed pp. 379 and 382, give the absolute labeling in (6.52).
Their diagrams (6.53)(b) and (6.57)(a) show the endpoint marking with the arm
exchange and the trivial star action, respectively.
