# Actual tensor cubes of degree-six division algebras do not split

This derived module, which supports `CentralDivisionTensorCubeProof`, proves
`Langlands.CentralSimple.centralDivision_degree_six_tensorCube_not_split`:
for every field `k` and actual finite-dimensional central division algebra
`D/k` with `Module.finrank k D = 36`, the actual algebra
`(D ⊗[k] D) ⊗[k] D` is not isomorphic to a full matrix algebra over `k`.
The matrix index may be `Fin m` for any natural number `m`; no positivity
premise on `m` is needed. The theorem is uniform in the universe and imposes
no characteristic restriction.

Choose the published actual finite Galois splitting field of `D`, with its
actual matrix chart. Dimension thirty-six forces chart size six; an actual
matrix reindexing produces a `Fin 6` chart. A hypothetical splitting of the
actual tensor cube has size 216, by multiplicativity of finite dimensions
and the dimension of a full matrix algebra. A second actual reindexing
carries it to the threefold product index `(Fin 6 × Fin 6) × Fin 6`.

The actual tensor-chart comparison from `TensorCubeScalarDefect` then
constructs a scalar cochain trivializing the cube of the original chart's
scalar defect. `SylowTwoOddSplitting` restricts that cochain to a Sylow
two-subgroup of the actual finite Galois group. The explicit finite-group
torsion calculation and Bezout identity trivialize the restricted defect;
the actual fixed-field chart therefore splits over the subgroup's fixed
field. This field has odd degree over `k`, contradicting the fact that an
actual splitting field of a degree-six division algebra has degree
divisible by six.

The route specializes the Sylow fixed-field proof of prime support of
index and exponent in Gille and Szamuely, *Central Simple Algebras and
Galois Cohomology* (2006), Proposition 4.5.8, Lemma 4.5.14 and Proposition
4.5.13, printed pages 103–105 (registered PDF pages 117–119). The general
prime-support theorem is not assumed: the supporting Lean modules implement
the needed scalar cochains, actual tensor-chart and fixed-field comparisons,
and splitting-degree divisibility directly.

The auxiliary theorem
`Langlands.CentralSimple.tensorCube_split_product_index` performs the size
count and the reindexing; it does not use centrality.

The published proposition
`Langlands.CentralSimple.CentralDivisionDegreeSixTensorCubeNonSplitStatement`
(positive matrix sizes only) is proved in `CentralDivisionTensorCubeProof` by
applying the theorem of this module, whose conclusion holds for every natural
matrix size. This module proves only the arithmetic statement. It neither
constructs a Tits obstruction of an E6 or E7 group nor compares one with this
tensor cube.
