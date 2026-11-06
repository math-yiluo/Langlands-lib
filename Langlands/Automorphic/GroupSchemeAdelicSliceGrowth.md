# Full adelic growth and original archimedean slices

This is an internal comparison between existing actual function spaces. The
field `F` is an arbitrary number field. For an affine group scheme `G` and a
specified algebraic representation `rho : G → GL_N` with `0 < N`, full
adelic moderate growth implies the existing polynomial growth on each fixed
finite slice. No connectedness, reductivity, closed-immersion or smoothness
hypothesis is needed for this implication. The function carrier remains
`ContinuousRationalFunctions F G`.

The matrix estimate itself holds for every natural matrix dimension `n`.
`AdelicMatrixHeight.infiniteLocal_le_matrixHeight` bounds each unnormalized
infinite-place matrix-and-inverse maximum by the existing archimedean matrix
height of the infinite projection. For a completion coordinate, the relevant
real or complex embedding is an isometry, so its norm is bounded by the mixed
real/complex product norm. Each mixed matrix entry is then bounded by the
original operator norm, using its maximum-row-sum formula. Applying this to
the matrix and its inverse gives the stated local bound.

Write `M = ∑ v : NumberField.InfinitePlace F, v.mult`. For a finite adelic
matrix `b`, `sliceHeightConstant F n b` is the nonnegative real number

```
n^M * ∏ᶠ v : FinitePlace F, finiteLocal F n (AdelicGL.pair F n 1 b) v.
```

The finite-place factors of `pair a b` are independent of `a`. Multiplying
the infinite-place estimates, with their existing multiplicities, proves
`height_pair_le`:

```
AdelicMatrixHeight.height F n (AdelicGL.pair F n a b)
  ≤ sliceHeightConstant F n b * (ArchimedeanGL.matrixHeight F n a)^M.
```

No norm is replaced and no properness theorem is used. The full height is
the existing dimension-scaled product of local matrix-and-inverse maxima;
the archimedean height is the original mixed-coordinate operator height.

`RepresentationGrowth.finiteMatrix`, imported from
`Langlands.Global.FiniteAdelicGroupCompactOpen`, evaluates `rho` on actual
finite adelic points and retains continuity. This module reuses that shared
helper without declaring a second copy. The two coefficient projection laws follow
from `MatrixRepresentation.affineMatrix_naturality` with the actual product
algebra projections. Hence `adelicMatrix_pair` identifies representation
evaluation on paired points with the original entrywise pairing of the
infinite and finite representation matrices. The matrix estimate therefore
pulls back to `adelicHeight_pair_le` for this specified representation.

If the original function has a full bound with coefficient `C ≥ 0` and
natural exponent `d`, its slice at `b` has coefficient `C * B^d` and exponent
`M*d`, where `B` is the slice constant of `finiteMatrix rho b`. Positivity of
the full height for `N > 0` justifies taking powers in the inequality.
`HasAdelicPolynomialGrowth.polynomialGrowth` proves exactly this implication.
`HasAdelicModerateGrowth.polynomialGrowth` first uses the already published
equivalence between the full real-exponent source-norm condition and the
full natural-exponent scaled-height condition. The resulting
`adelicGrowth_le_polynomialGrowth` is inclusion of subrepresentations under
the original full positive right action. Intersecting with the existing
finite plot-smooth subrepresentation retains its smooth slices and one common
open finite stabilizer.

For the actual general linear group scheme with its standard representation,
`adelicGrowthGeneralLinearMap` is a complex linear injection into the original
`Langlands.Automorphic.PolynomialGrowthRationalFunctions F n`.
`finitePlotSmoothAdelicGrowthGeneralLinearMap` is a complex linear injection
into the original `finiteSmoothPolynomialGrowthSubrepresentation`.
Both are the existing genuine slice-growth linear equivalence composed with
the proved submodule inclusion. Their underlying continuous functions are
exactly `continuousGeneralLinearEquiv`; both intertwine the original full
positive adelic translations `R(g)f(x) = f(x*g)`.

This construction uses the existing height, coefficient-point, product-point,
function and slice-growth APIs as its provenance. It does not prove the
converse growth implication, surjectivity of either injection, automatic
uniform growth, representation independence, properness, tensor-factorization,
or an equivalence of automorphic forms. Those assertions require their own
comparisons and hypotheses.
