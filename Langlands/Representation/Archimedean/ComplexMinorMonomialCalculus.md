# Minor monomials on `GL_n(ℂ)`: equivariance, smoothness, right derivatives, `U(n)`-finiteness

Lean module: `Langlands.Representation.Archimedean.ComplexMinorMonomialCalculus`.

Worker 5677 wrote this module, with Worker 728 as coauthor. It is part of Task 7064
(`e4a22cc7-0a28-44a3-afc6-38bb7c243851`). It is a helper module for the product lemma
`ComplexMinorProductCyclic`, step P1 of Worker 728's route to the Library statement
`ComplexTemperedStandardIrreducibleStatement`. The module contains no statements (`Prop`
definitions); it defines auxiliary functions and proves lemmas about them, all in the
namespace `Langlands.Archimedean.ComplexMinorProduct`.

Notation. The Library module `ComplexLowestKTypeMultOne` (namespace `ComplexLowestKType`)
defines:

* `botIdx j`, `topIdx j : Fin (j + 1) → Fin n`: the bottom `j + 1` indices
  `n − (j + 1), …, n − 1` and the first `j + 1` indices `0, …, j`;
* `minor j g = Δ_{j+1}(g)`: the determinant of the submatrix of `g` on the rows `botIdx j` and
  the columns `topIdx j`;
* `minorMonomial c d g = det(g)^d · ∏_j Δ_{j+1}(g)^{c_j}`, for `c : Fin n → ℕ`, `d : ℤ`.

Write `v = minorMonomial c d`.

## Definitions

* `minorWeight c d i = d + ∑_{j : n − (j + 1) ≤ i} c_j ∈ ℤ`. This is the weight of `v` at
  position `i`: the exponent of `b_ii` in `minorMonomial_upper_mul` below.
* `rightChar c d y = det(y)^d · ∏_j (∏_{t ≤ j} y_tt)^{c_j}`. This is the right character of `v`
  on upper triangular matrices.
* `minorFun c d : GL_n(ℂ) → ℂ`: `g ↦ v(g)`.
* `rightCharDeriv c d X = (d/dt) rightChar c d (1 + tX) |_{t = 0}` (a real derivative, `t ∈ ℝ`).
* `minorPoly c`: the polynomial `∏_j Δ_{j+1}^{c_j}` as a function of the entry vector
  `Fin n × Fin n → ℂ`, read through `LevelFunctions.toMat`.
* `rightMulEntries k`: right multiplication by the matrix `k` on entry vectors.
* `detWeightMap d`: the linear map from functions `P` of the entry vector to functions on
  `GL_n(ℂ)`, `P ↦ (g ↦ det(g)^d · P(entries of g))`.
* `revUnitary n`: the antidiagonal permutation matrix (`Fin.revPerm`), as an element of the
  unitary group. It is `ComplexPermutation.permUnitary Fin.revPerm`.

Provenance. These are internal definitions for the proof of the product lemma. Minors of this
shape, `Δ_{j+1}` on the bottom rows and the first columns, and their monomials are the
lowest-`U(n)`-type vectors of the Library module `ComplexLowestKTypeMultOne`. The weights and
the right character are the standard computation of how a product of such minors transforms
under the upper triangular Borel subgroup.

## Results

Minors of products (no hypotheses beyond those listed):

* `submatrix_mul_of_vanish`: `(A B).submatrix r c = A.submatrix r s · B.submatrix s c` when `s`
  is injective and every term `A (r i) p · B p (c j)` with `p` outside the range of `s` is zero.
* `topIdx_strictMono`.
* `minor_upper_mul`: for `b` upper triangular,
  `Δ_{j+1}(b g) = (∏_t b_{botIdx j t, botIdx j t}) · Δ_{j+1}(g)`.
* `minor_mul_upper`: for `y` upper triangular,
  `Δ_{j+1}(g y) = Δ_{j+1}(g) · ∏_t y_{topIdx j t, topIdx j t}`.

Equivariance:

* `prod_botIdx`: `∏_t f(botIdx j t) = ∏_{i ∈ bot j} f(i)`.
* `minorMonomial_upper_mul`: for `b` upper triangular with all `b_ii ≠ 0`,
  `v(b g) = (∏_i b_ii^{minorWeight c d i}) · v(g)`.
* `minorMonomial_mul_upper`: for `y` upper triangular, `v(g y) = v(g) · rightChar c d y`.

Smoothness:

* `contDiff_submatrix`, `contDiff_minor`: submatrices and minors are smooth (real `C^∞`).
* `contDiffOn_det_zpow`, `contDiffOn_minorMonomial`: `det^d` and `v` are smooth on the open set
  of invertible matrices.
* `contMDiff_minorFun`: `minorFun c d` is smooth on `GL_n(ℂ)` for the manifold structure
  `matrixModel ℂ n`.

Right derivatives:

* `isUpperTriangular_one_add_smul`: `1 + tX` is upper triangular when `X` is.
* `rightDerivative_minorFun`: for `X` upper triangular and `g ∈ GL_n(ℂ)`,
  `rightDerivative (matrixModel ℂ n) X (minorFun c d) g = rightCharDeriv c d X · v(g)`.

`U(n)`-finiteness:

* `minor_mem_degLE`, `minorPoly_mem_degLE`: `Δ_{j+1}` has degree at most `n` in the entries,
  and `minorPoly c` has degree at most `∑_j c_j · n`
  (`RealPolynomialFunctions.degLE`: the span of monomials of total degree at most the bound in the
  entries `v_p` and their conjugates `conj (v_p)`).
* `coord_rightMulEntries_mem_degLE`: each coordinate of `rightMulEntries k` has degree at most 1.
* `rightTranslation_minorFun`: the right translate of `minorFun c d` by `k` is
  `det(k)^d • detWeightMap d (minorPoly c ∘ rightMulEntries k)`.
* `minorFun_mem_kFiniteVectors`: `minorFun c d` is `U(n)`-finite for right translation (its
  translates span a finite-dimensional space).
* `mul_mem_kFiniteVectors`: the pointwise product of two `U(n)`-finite functions is `U(n)`-finite.

Nonvanishing:

* `submatrix_revPerm`: the submatrix of the antidiagonal permutation matrix on the rows
  `botIdx j` and columns `topIdx j` is the antidiagonal permutation matrix of size `j + 1`.
* `minor_revPerm_ne_zero`, `minorMonomial_revUnitary_ne_zero`: `Δ_{j+1}` and `v` do not vanish
  at `revUnitary n`. In general `v(1) = 0`, since `Δ_{j+1}(1) = 0` for `j < n − 1`.

## Proofs

* `submatrix_mul_of_vanish`: entrywise, the matrix-product sum over `Fin n` reduces to the sum
  over the range of `s` (`Fintype.sum_of_injective`).
* `minor_upper_mul`: apply `submatrix_mul_of_vanish` with `s = botIdx j`. A term `b_{r,p} g_{p,c}`
  with `p` below the bottom block (`p < n − (j + 1) ≤ r`) vanishes because `b` is upper
  triangular. Then `det_mul`. The square block of `b` on the bottom indices is upper
  triangular, so its determinant is the product of its diagonal (`det_of_isUpperTriangular`).
  `minor_mul_upper` is the same argument with `s = topIdx j` on the column side.
* `minorMonomial_upper_mul`: expand with `minor_upper_mul`, `det_mul` and
  `det_of_isUpperTriangular`. Rewrite the products over `botIdx j` as products over `bot j`.
  Exchange the products over `j` and `i` (`Finset.prod_comm'`). Collect the exponents:
  `b_ii` appears in `Δ_{j+1}` exactly when `i ∈ bot j`, that is when `n − (j + 1) ≤ i`.
* `minorMonomial_mul_upper`: expand with `minor_mul_upper` and `det_mul`; `ring`.
* Smoothness: `det` is smooth (`ComplexMaximalParabolicIntegration.contDiff_det`), and a
  submatrix is a continuous real-linear map. For `d < 0`, `det^d = (det^{|d|})⁻¹` is smooth
  where `det ≠ 0` (`ContDiffOn.inv`). Then `contMDiff_of_contDiffOn` gives smoothness on
  `GL_n(ℂ)`.
* `rightDerivative_minorFun`: by `rightDerivative_eq_fderiv`, the right derivative is the
  derivative of the extension of `v` to all matrices along the line `t ↦ g + t g X`. Near
  `t = 0` the line stays in the invertible matrices (`isOpen_setOf_isUnit_matrix`), where it
  equals `g (1 + tX)`. By `minorMonomial_mul_upper` the function there is
  `t ↦ v(g) · rightChar c d (1 + tX)`. Its derivative at `0` is `v(g) · rightCharDeriv c d X`
  (`Filter.EventuallyEq.deriv_eq`, `deriv_const_mul_field`).
* `minorFun_mem_kFiniteVectors`: every right translate lies in the image under `detWeightMap d`
  of the finite-dimensional space `degLE (∑_j c_j · n)` (`rightTranslation_minorFun`,
  `comp_mem_degLE`), so the span of the translates is finite-dimensional
  (`Submodule.finiteDimensional_of_le`).
* `mul_mem_kFiniteVectors`: the translates of `f h` lie in the product `S₁ · S₂` of the spans of
  the translates of `f` and of `h`. This product is finitely generated (`Submodule.FG.mul`).
* `submatrix_revPerm`: entrywise, `rev(botIdx j t) = topIdx j t'` if and only if `rev t = t'`
  (`omega`). `minor_revPerm_ne_zero`, `minorMonomial_revUnitary_ne_zero`: the determinant of a
  permutation matrix is its sign, a unit (`Matrix.det_permutation`).
