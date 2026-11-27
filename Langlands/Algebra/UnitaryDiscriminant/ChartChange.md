# Change of matrix coordinates in the unitary discriminant

`relativeDiscriminantClass_eq_of_chart` shows that two matrix charts over the
same splitting field give the same relative discriminant class. The base,
quadratic center, and splitting field share a universe. The algebra itself
has an independent universe.

Skolem–Noether expresses the change of matrix chart as conjugation by an
invertible matrix \(T\). If \(P_g\) are the lifts from the first chart, the
second chart can use \(T P_g (g\star T)^{-1}\), where \(g\star\) is the entrywise
action followed by inverse transpose on the outer coset. The scalar factor
set of these lifts is unchanged. In the determinant factor set, the extra
factor is the ordinary coboundary of the cochain with value \(g(\det T)\) on
the outer coset and \(1\) on the stabilizer of the center. This follows by
applying the determinant to the conjugated lifts and using the index-two
coset multiplication law. The relative classes therefore agree by
`BrauerComparison.unitClass_eq_of_coboundary_mul`.

The calculation is derived from the determinant factor set for the middle
exterior power descent in `Langlands.Algebra.UnitaryDiscriminant.Class`.
