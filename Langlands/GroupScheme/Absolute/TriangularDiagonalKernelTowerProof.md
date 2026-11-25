# Character-linear towers for the supplied triangular diagonal image

`Langlands.GroupScheme.triangularDiagonalKernelTower.{u}` proves exactly
`Langlands.GroupScheme.TriangularDiagonalKernelTowerStatement.{u}`.
The universe and field are arbitrary. The conclusion applies to the supplied
actual diagonalizable group `D(Λ)` and homomorphism `q`, for every matrix size
including zero. The source is affine and locally of finite type, with the
closed triangular inclusion required by the statement. The character group
is finitely generated and may have torsion. There is no additional smoothness,
reducedness, connectedness, perfectness or characteristic restriction.

The proof introduces the hypotheses and applies the published theorem
`TriangularLayer.admitsTower_diagonalizable_of_affine_image_and_normal_quotient`
from `Langlands.GroupScheme.Absolute.TriangularActualQuotientTower`. It supplies
`affineHomImage` from `Langlands.GroupScheme.AffineHomImageProof` and
`affineNormalSubgroupQuotient` from
`Langlands.GroupScheme.AffineNormalSubgroupQuotientProof` for that construction's
two proposition-valued premises. Both are published proofs in the same
universe. The remaining arguments are exactly the original `j`, its closed
inclusion witness, `Λ`, `d`, `q`, the factorization and the full-kernel fppf
quotient witness. The closedness premise on `d` is unused because the imported
construction proves a stronger result without it.

The resulting tower is for this very `q`. Each transition is an fppf quotient
by its full actual scheme kernel, embedded as a closed subgroup of the
additive group with conjugation through a character of the fixed `D(Λ)` on
all test schemes. Kernels may be finite, nonreduced or trivial. The terminal
structural map is an actual isomorphism. These properties, including the
zero-size case, are provided by the imported construction, whose paired
Markdown explains its coordinate-series induction and quotient comparisons.
No section is asserted by this theorem.

This is an internal derived proof assembling published Library results. The
source relationship to Milne (2022), Theorem 16.21, is documented by the
unchanged statement pair and the imported tower construction. The statement
pair and every pair it imports are unchanged.
