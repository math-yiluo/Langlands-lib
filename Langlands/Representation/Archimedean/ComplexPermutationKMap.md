# `U(n)`-isomorphic principal series

Module `Langlands.Representation.Archimedean.ComplexPermutationKMap`, namespace
`Langlands.Archimedean.ComplexPermutation`. This internal helper module for
`ComplexStandardPermutationStatement` has no literature source.

Restricted to `U(n)`, the principal series of the characters `d 0, …, d (n-1)` and of their
rearrangement `d (σ⁻¹ 0), …, d (σ⁻¹ (n-1))` are isomorphic. Both are induced from the diagonal
unitary torus, and the permutation matrix of `σ` conjugates the two torus characters. The module
constructs an injective `U(n)`-equivariant linear map
`permKMap d σ : X(List.ofFn d) → X(List.ofFn (d ∘ σ⁻¹))`. These maps, in both directions, are
what the upgrade lemmas of `ComplexPermutationKType` need.

## Declarations

* `permUnitary σ`: the permutation matrix `P = σ.permMatrix ℂ` (`P i j = 1` exactly when
  `j = σ i`) as a unitary matrix. `permMatrix_mul_diagonal`: `P m = diag(m (σ j) (σ j)) P` for
  diagonal `m`.
* `evalPerm ds σ`: the functional `f ↦ f(P)`. `isTorusEigenfunctional_evalPerm`: it transforms
  under a diagonal unitary `m` by the rearranged weights,
  `f(P m) = f(diag(m (σ j) (σ j)) P) = ∏ⱼ m (σ j) (σ j)^{l_j} f(P) = ∏ₖ m k k^{l_{σ⁻¹ k}} f(P)`.
  This uses the principal series law, `principalSeriesCharacter_ofFn` and `|m j j| = 1`.
* `permExponent d σ k = 2 t_{σ⁻¹ k} + (n - 1) - 2k` and `permFunction d σ f`: the Frobenius
  function `frobeniusFunction` (from `ComplexJacquetFrobeniusFunction`, Task 7088) of
  `evalPerm`, that is `F(β κ) = χ'(β) f(P κ)` for `β` upper triangular and `κ` unitary, where
  `χ'` is the Borel character with the rearranged weights and exponents.
* `permFunction_mem`: `F` is smooth (`contMDiff_frobeniusFunction`, using that `X(List.ofFn d)`
  is a `(𝔤𝔩_n(ℂ), U(n))`-module) and satisfies the principal series law of the rearranged list
  (`frobeniusFunction_diagonal_mul` with `principalSeriesCharacter_ofFn`).
* `permFunction_rightTranslation`: `F_f(g k) = F_{ρ(k) f}(g)` (`frobeniusFunction_mul_unitary`).
  `permFunction_mem_kFinite`: hence the right translates of `F_f` lie in the image of the
  finite-dimensional orbit span of `f`, and `F_f` is `U(n)`-finite.
* `permKMap d σ`: `f ↦ F_f` as a linear map between the `U(n)`-finite functions.
  `permKMap_equivariant`: it commutes with right translation by `U(n)`.
  `permKMap_injective`: `F_f(P⁻¹ κ) = f(P P⁻¹ κ) = f(κ)` for unitary `κ`
  (`frobeniusFunction_eq` with the trivial upper triangular factor), so `F_f = 0` forces `f` to
  vanish on `U(n)` and hence `f = 0` (`kFiniteEval_one_separating`).
