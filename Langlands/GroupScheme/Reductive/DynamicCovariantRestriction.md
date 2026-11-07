# Actual opposite-unipotent restriction of entire covariant spaces

Worker 1369 derives this construction from the published opposite-cell
theorem, actual represented dynamic subgroups, the basic-open argument
implemented in `SplitPinning.exists_cellCoordinate`, full covariant cell
restriction and the actual Hopf/Lie coordinate comparison. This is an
internal specialization; it asserts no additional literature theorem.

Let `G` be an affine group over an arbitrary field `k : Type u`,
`i : T → G` a torus morphism, and `ν` a cocharacter of `T`. Put
`P = Dynamic.Affine.parabolicScheme (groupHom ν ≫ i)` and
`U = Standard.unipotentScheme i (-ν) ∅`, with their actual inclusions.
The restriction maps are defined without a connected-reductivity,
smoothness, maximal-torus, root-datum or representation hypothesis.

For connected reductive `G` and split `T`,
`exists_oppositeUnipotentCellCoordinate` proves that a non-zero-divisor
coordinate has its entire unit locus inside `P · U`. The published
opposite-cell theorem makes `U × P → G` an open immersion containing the
identity. A basic open around that point lies in its image. Applying the
coordinate antipode reverses the factors. The resulting coordinate is
nonzero because its identity value is a unit; the actual coordinate
algebra of connected reductive `G` is a domain, so it is a
non-zero-divisor. Every factorization is on the original relative scheme
test. There is no affine, reduced, nonempty or rational-point restriction
on that test.

For every coordinate `χ` of `P`, `oppositeUnipotentRestriction` restricts
the entire `AffineCoordinates.leftCovariantSubspace iP χ` along the
actual `U → G`, then uses `lieCoordinateAlgEquiv U` to reach
`CharacterUnits.Coord U`. No cyclic subspace is substituted.
Under the connected-reductivity and split-torus hypotheses, the cell
coordinate and the published full-space restriction theorem prove that
this map is injective. The proof compares evaluations on the whole unit
locus using covariance; the non-zero-divisor detects equality in the
original coordinate algebra.

In exponential characteristic `p`, at any height `r`,
`oppositeUnipotentFrobeniusRestriction` composes this full restriction
with the actual `FrobeniusCoordinateModel.quotientMap U p r`.
Its application formula and zero criterion identify its kernel exactly:
the full restriction belongs to the actual Frobenius image of the
augmentation ideal.

The final map is defined for every `χ`, including powers of the canonical
negative-rho coordinate. This construction does not assert its
injectivity at a fixed height, a polynomial degree bound, a whole-space
Steinberg dimension bound or the host `SteinbergBigCellStatement`.
