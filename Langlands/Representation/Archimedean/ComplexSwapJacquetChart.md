# The rank-one chart and the integrand of the swapped Jacquet functional

Module `Langlands.Representation.Archimedean.ComplexSwapJacquetChart`, namespace
`Langlands.Archimedean.ComplexSwapJacquet`. This internal helper module for
`ComplexStandardPermutationStatement` has no literature source. It holds only definitions shared
by the modules `ComplexSwapJacquetDecay`, `ComplexSwapJacquetLie`,
`ComplexSwapJacquetFunctional` and `ComplexSwapJacquetProof`, which together build the rank-one
Jacquet functional of an adjacent swap.

Fix adjacent positions `i` and `j` of `GL_n(ℂ)`, given as `Fin n` with `hj : (j : ℕ) = i + 1`.

## Declarations

* `ne_of_val_eq_succ hj : i ≠ j`.
* `chart i j hj z : GL_n(ℂ)` for `z : ℂ` is the product
  `Matrix.GeneralLinearGroup.swap ℂ i j * Matrix.GeneralLinearGroup.transvection i j _ z`. It is
  the permutation matrix `s` of the transposition `(i j)` times the upper unipotent matrix
  `x(z) = 1 + z E_ij`. As a matrix it is the identity, except that rows and columns `i, j` hold
  the block `[[0, 1], [1, z]]`. `chart_val` says the underlying matrix is
  `Matrix.swap ℂ i j * Matrix.transvection i j z` (holds by `rfl`).
* `kappa ds hn k c` for a list `ds` of complex character data with `hn : ds.length = n`, a
  position `k : Fin n` and `c : ℂ` is
  `Re c · (2 t_k + (n - 1) - 2k) + Im c · (i l_k)`,
  where `t_k = (ds.get k).exponent` and `l_k = (ds.get k).weight`. It is the real-linear
  function of `c` whose values at `c = 1` and `c = i` are the two exponents
  `2 t_k + (n - 1) - 2k` and `i l_k` of position `k` in the Jacquet-functional convention
  (`IsComplexJacquetFunctional`, Library module `ComplexJacquetReduction`).
  `ComplexSwapJacquetLie` proves `R(c E_kk) f (1) = kappa ds hn k c · f(1)` for `f` in the
  standard module of `ds` (`rightDerivative_one_diag`).
* `integrand ds hn i j hj c f z` is
  `R(c E_jj) f (s x(z)) - kappa ds hn j c · f(s x(z))`, with `R(X) f` the right derivative
  `rightDerivative (matrixModel ℂ n) X f`. Its integral over `z ∈ ℂ` is the rank-one Jacquet
  functional `Λ_c(f)` of `ComplexSwapJacquetFunctional`.

The module states no theorems beyond `ne_of_val_eq_succ` and `chart_val`.
