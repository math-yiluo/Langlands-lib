# Compact Tate-normalized representatives of connected CM classes

`CompactTateCMRepresentative` packages the original pointed Harris level
data over a connected admissible CM base together with its determinant and
numerical conditions and the compact orbit lattice equality
`HarrisCompactTateNormalized`. The admissible base supplies local
noetherianity, quasi-separatedness, the torsion units, the finite étale
roots of unity, the dual data and the pair additivity used by the class
tower. The construction takes the Picard and tensor prerequisites, finite
Weil transition compatibility, the rational comparison for the profinite
integer adeles and the torsion finite étale statement.

`exists_compactTateCMRepresentative` starts with a representative of the
given pointed class using `HarrisNumericalWeilLevel.classOf_surjective`.
The geometric point has characteristic zero because the base is over
the CM field. The proof combines the two class conditions into the
determinant and dimension condition, applies `exists_harrisCompactTateNormalized`,
then recovers the two class conditions for the resulting representative.
Its class is the input class at the original level.

`compactTateCMPointMap_normalized` uses the compact orbit lattice comparison
to transport the equality to any second point along an isomorphism of the
finite étale fibre functors. Point transport keeps the same polarized
abelian scheme and rational action. The compatibility equation defining
an unpointed class then shows that the transported representative gives
its value at the second point, by `compactTateCMPointMap_pointedClass`.
