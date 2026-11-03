# Compact subgroup and covering assembly from coordinates

This is derived group-theoretic and topological infrastructure for the adelic
Iwasawa argument. It constructs no local compact subgroup and proves no local
Iwasawa theorem. In particular, it does not prove
`AdelicGroupPoints.ParabolicIwasawaStatement`.

For group homomorphisms `π i : A → H i` and local subgroups `K i`,
`coordinateSubgroup π K` consists of the elements whose every coordinate belongs
to the specified subgroup. `CompactProductLift π K` is data of a continuous map
from the full product of the `K i` to `A` with the specified coordinates. It does
not assume that this map is a homomorphism, that the local groups are compact, or
that the coordinate subgroup is maximal.

When the coordinates distinguish points, `range_lift` identifies the lift's range
with the coordinate subgroup. If every local subgroup is compact, product
compactness and continuity give `isCompact_coordinateSubgroup`. Supported tuples
in the product show that each projection of the coordinate subgroup is exactly
`K i`, in `map_coordinateSubgroup`. The theorem `maximal_coordinateSubgroup`
projects any compact subgroup containing the coordinate subgroup to each local
group, applies the assumed local maximality among all compact subgroups, and
recovers inclusion in the coordinate subgroup. The combined theorem
`compact_maximal_coordinateSubgroup` returns compactness and unrestricted
maximality. These arguments require only the displayed topology and continuity
assumptions; they impose no Hausdorffness or topological-group assumptions.

The covering theorem `range_mul_coordinateSubgroup_eq_univ` takes an actual
global source group `B`, local source groups `Q i`, compatible homomorphisms
`f`, `ρ i`, and `φ i`. Its assumptions are local right-compact covering,
membership of every ambient element in the chosen local subgroups at all but
finitely many indices, and lifting of every source family that is the identity
at all but finitely many indices. For an element `a`, it chooses the local source
factor to be the identity wherever `π i a` already belongs to `K i`; elsewhere
it chooses a factor from the local covering equality. The resulting source
family has finite support, so it lifts to `b : B`. The element `(f b)⁻¹ * a`
belongs to the coordinate subgroup, proving the exact equality with the source
range on the left and the compact factor on the right.

The motivation is Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Theorem 2.7.1, equation (2.24), printed p.71, and Appendix B's local to
global proof sketch. The implemented abstract lemmas and their assumptions are
derived infrastructure, rather than a translation of an additional theorem in
the book. The actual adelic coordinate maps, continuous lift, local compact
subgroups, local maximality, local covering, and almost-everywhere membership
remain separate inputs. No supplied datum here discharges their existence.
