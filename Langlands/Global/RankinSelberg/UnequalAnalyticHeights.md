# Height bounds for Siegel coordinates with a fixed basis column or row

Provenance: internal. This module is a supporting lemma module for the proof of
`Langlands.Global.RankinSelbergGlobal.UnequalAnalyticStatement` (Cogdell 2004, Theorem 2.1).
Cogdell states the convergence of the unequal-rank global integral as a consequence of the
rapid decay of cusp forms. The Lean proof derives the needed decay from the Library's
Siegel decomposition. This module supplies the height bounds used there: if `γ g = A(X) q`
with `γ` rational, `q` in a fixed compact set, and `A(X)` the archimedean torus element with
entries `exp (X i)`, then a column of `g` that is a standard basis column bounds some `X k`
below, and a row of `g` that is a standard basis row bounds some `X k` above. The argument
is the classical one: a product-formula lower bound for heights of rational vectors, and an
upper bound for heights of rows and columns of matrices in a compact set.

Notation: `torInf F n X` is the archimedean torus element of
`Langlands.Automorphic.CuspidalL2.Basics`, `A(X) := AdelicGL.ofInfinite F n (torInf F n X)`,
`d := [F : ℚ]`, `PrimitiveAdelicHeight.height F n` is the adelic height of a vector
(`Langlands/Global/PrimitiveAdelicHeight*`), `AdelicMatrixHeight.height F n` is the adelic
height of an invertible matrix, and `PrimitiveAdelicHeight.rational F n v` is the image of a
rational vector `v` in `𝔸^n`. All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.UnequalAnalytic`.

## Declarations

- `torus_mulVec_rational_apply X v`: `A(X) *ᵥ v` has coordinates `exp (X i) · v i`
  (as `realScale F (exp (X i)) * diagonal F (v i)`). Proof: `ofInfinite_torInf_val`
  identifies `A(X)` with a diagonal matrix, then `Matrix.mulVec_diagonal`.
- `exp_le_height_torus_rational X v k hk` (**product formula lower bound**): if
  `v k ≠ 0`, then `exp (d X k) ≤ height (A(X) *ᵥ v)`. Proof: let `t` be the principal
  idele of `v k`; its full idele norm is `1` (`IdeleAbsoluteValue.full_diagonalUnits`). At
  each infinite place `w` the local maximum norm of `A(X) *ᵥ v` is at least the `k`-th
  coordinate norm `exp (X k) ‖t_w‖`, and at each finite place it is at least `‖t_p‖`.
  Multiplying over the infinite places with multiplicities (whose sum is `d`) and over the
  finite places (`finprod_le_finprod₀`) gives `exp (d X k) · 1 ≤ height`.
- `finprod_le_of_le_of_one_le` (private): a factorwise bound for finite products when the
  larger factors are at least `1` and have finite multiplicative support, with no support
  hypothesis on the smaller factors.
- `height_le_matrixHeight_of_local hn g x hinf hfin`: a vector whose local maximum norms are
  at most the local norms of `g` (`AdelicMatrixHeight.infiniteLocal`, `finiteLocal`, which
  take both `g` and `g⁻¹` into account) has height at most `AdelicMatrixHeight.height F n g`.
  The infinite factors use the slack `n ≥ 1` built into the matrix height.
- `height_column_le hn g j`, `height_row_le hn g i`: a column, respectively a row, of `g`
  has height at most the matrix height of `g`. Proof: each entry is at most the local
  maximum (`MatrixInverseHeight.entry_le_localMaximum`), then the previous lemma.
- `exists_matrixHeight_le_of_isCompact hn hQ`: matrix heights are bounded by some `B ≥ 1`
  on a compact set (continuity of the matrix height, `AdelicMatrixHeight.continuous_height`).
- `realScale_exp_neg_mul s a`: `realScale (exp (-s)) * (realScale (exp s) * a) = a`.
- `exists_coordinate_bounds hn hQ` (**coordinate bounds**): for a compact `Q` there is `C`
  such that, whenever `γ g = A(X) q` with `γ ∈ GL_n(F)` and `q ∈ Q`,
  1. if some column `j` of `g` is the standard basis column `e_j`, then `-C ≤ X k` for some
     `k`;
  2. if some row `i` of `g` is the standard basis row `e_i`, then `X k ≤ C` for some `k`.

  Here `C = log B / d`, with `B` the bound on matrix heights over `Q`.
  Proof of 1: column `j` of `q = A(-X) γ g` is `A(-X)` applied to the rational column
  `γ e_j`. That column is nonzero because `γ` is invertible, so it has a nonzero coordinate
  `k`. The product-formula bound gives `exp (-d X k) ≤ height(column j of q) ≤ B`.
  Proof of 2: from `g q⁻¹ = γ⁻¹ A(X)`, row `i` of `q⁻¹` is `A(X)` applied to the rational row
  `e_i γ⁻¹`, which has a nonzero coordinate `k`. Then
  `exp (d X k) ≤ height(row i of q⁻¹) ≤ height(q⁻¹) = height(q) ≤ B`
  (`AdelicMatrixHeight.height_inv`).
