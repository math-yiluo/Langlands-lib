# The split matrix of a quaternionic line rotation

Module `Langlands.GroupScheme.Quaternionic.LineRotationSplit`, namespace
`Langlands.GroupScheme.Quaternionic`.

Let `D` be a division algebra over a field `F`, `L` a field over `F` and
`e : L ⊗ D ≃ M₂(L)` a splitting. `chartN e n L` (module
`Quaternionic/QuaternionicMoritaIsometryProof`) turns an element of `L ⊗ M_n(D)` into a
`2n × 2n` matrix over `L` (Morita splitting). `coefficientEquiv F D L` identifies
`L ⊗ M_n(D)` with `M_n(L ⊗ D)`.

* `rank_chartN_vecMulVec`: for row vectors `a, b ∈ (L ⊗ D)ⁿ`, the split matrix of the
  rank-one update `vecMulVec a b` has rank at most `2`. Its block matrix `matrixChartR`
  factors as `A * B`, with `A` of size `(n × 2) × 2` built from the charts of the entries
  of `a` and `B` of size `2 × (n × 2)` from those of `b`. So the rank is at most the width
  `2` of `A` (`Matrix.rank_mul_le_left`, `Matrix.rank_le_card_width`); reindexing does not
  change the rank (`Matrix.rank_reindex`).
* `rank_chartN_lineRotationMatrix_sub_one`: for a first-kind involution `σ`, a form
  `q : σ.QuadraticForms (Fin n)`, a vector `x` and `t ∈ L ⊗ D`, the split matrix of the line
  rotation `lineRotationMatrix σ q x L t` (module `Quaternionic/LineRotation`) differs from
  the identity by a matrix of rank at most `2`. The difference is the negative of the split
  matrix of the rank-one update `vecMulVec (lineColumn) (lineRow t)`, and negation is
  multiplication by `-1`.

For rotations of a nondegenerate quaternionic line, the bound expresses that the
rotation minus the identity has image in a scalar plane after splitting. The matrix
bound follows directly from the definitions.
