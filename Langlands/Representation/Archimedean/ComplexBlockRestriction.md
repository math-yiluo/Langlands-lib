# Restriction of complex standard modules to a `GL_2(ℂ)` block

Module `Langlands.Representation.Archimedean.ComplexBlockRestriction`, namespace
`Langlands.Archimedean.ComplexBlock`. This is an internal helper module for
`ComplexStandardUnlinkedSwapReductionStatement` (module `ComplexStandardUnlinkedSwapReduction`).
It has no literature source. It imports the rank-one Jacquet functional modules
`ComplexSwapJacquetProof` and `ComplexSwapJacquetNonvanishing` and the statement module
`ComplexGLTwoUnlinkedIrreducible`.

## Notation

Fix `n`, a position `p` with `hp : p + 2 ≤ n`, lists `pre` (with `hpre : pre.length = p`) and
`post`, and complex characters `d`, `e`. Put `ds = pre ++ d :: e :: post`, so `d` and `e` sit
at the positions `p` and `p + 1` (counting from `0`). Write `X_N(cs)` for
`KFs N cs = kFiniteFunctions (complexStandardModule N cs) (unitaryCompact ℂ N)`, the
`U(N)`-finite functions of the standard module of `cs` on `GL_N(ℂ)`. For a character `d` with
weight `l_d` and exponent `t_d`, put

* `shift n p = (n - 2 - 2p)/2`;
* `twist s d = characterOfParams l_d (t_d + s)`, the character with the same weight and exponent
  `t_d + s`;
* `d' = twist (shift n p) d` and `e' = twist (shift n p) e`.

## The block embedding

* `pos p hp k = p + k` for `k : Fin 2`, the two block positions.
* `incl p hp` is the `n × 2` matrix `P` of the coordinate inclusion. `lin p hp X = P X Pᵀ` puts
  the `2 × 2` matrix `X` in rows and columns `p`, `p + 1` and zeros elsewhere. `lin` is
  additive, multiplicative, `ℂ`-linear (`linL`) and commutes with `star`.
  `lin_single`: `lin (E_kl c) = E_{pos k, pos l} c`.
* `blockMat p hp M = P M Pᵀ + (1 - P Pᵀ)` is the identity matrix with `M` in the block. It is
  multiplicative (`blockMat_mul`, `blockMat_one`, `blockHom`), commutes with `star`, and
  satisfies `blockMat M * lin X = lin (M X)` (`blockMat_mul_lin`).
* `block p hp : GL_2(ℂ) →* GL_n(ℂ)` is `blockMat` on units. It maps `U(2)` into `U(n)`
  (`block_mem_unitaryCompact`, `blockU`) and upper unipotent matrices to upper unipotent
  matrices (`block_mem_upperUnipotent`). It maps the diagonal matrix of `a : Fin 2 → ℂˣ` to the
  diagonal matrix of `blockDiag p hp a`, which has `a 0`, `a 1` at `p`, `p + 1` and `1`
  elsewhere (`block_diagonalUnits`).
* `blockMat_swap`, `blockMat_transvection` and `block_chart`:
  `block (chart 0 1 z) = chart (pos 0) (pos 1) z`. Here `chart i j z` is the chart
  `s x(z) = swap_{ij} · transvection_{ij}(z)` of `ComplexSwapJacquetChart`.

## Restriction to the block

* `restrictLin p hp f = f ∘ block`. `contMDiff_restrictLin`: restriction preserves smoothness,
  because `unitsExtension f ∘ blockMat` is smooth on the open set of invertible `2 × 2`
  matrices (`contDiffOn_unitsExtension`) and `blockMat` is affine.
* `principalSeriesCharacter_blockDiag`: the character of `ds` at `blockDiag a` equals the
  character of `[d', e']` at `a`. The factors outside the block are `1`, and at the block the
  normalized exponents agree: `t_d + (n - 1 - 2p)/2 = (t_d + s) + 1/2` and
  `t_e + (n - 3 - 2p)/2 = (t_e + s) - 1/2` for `s = (n - 2 - 2p)/2`.
* `restrictLin_mem_complexStandardModule`: if `f` is in the standard module of `ds`, then
  `f ∘ block` is in the standard module of `[d', e']`. This is the transformation law of `f` at
  `blockDiag a`, `block u` and `block g`.
* `restrictLin_mem_kFiniteVectors`: the `U(2)`-translates of `f ∘ block` are restrictions of
  `U(n)`-translates of `f` (`restrictLin_rightTranslation`). So their span lies in the image of
  the finite-dimensional `U(n)`-orbit span of `f`.
* `res p hp pre post d e hpre : X_n(ds) →ₗ[ℂ] X_2([d', e'])` is the restriction map, with
  `res_apply : (res f)(g) = f(block g)`.
* `res_rep`: `ρ_2(k)(res f) = res(ρ_n(blockU k) f)` for `k ∈ U(2)`.
* `rightDerivative_restrictLin` and `res_lie_one_tmul`: `R(X)(res f) = res(R(lin X) f)`. Both
  right derivatives are Fréchet derivatives of the units extensions
  (`rightDerivative_eq_fderiv`). Near `m`, the units extension of `f ∘ block` agrees with
  `unitsExtension f ∘ blockMat`. Then the chain rule applies, with derivative `lin` of
  `blockMat`, and `lin (m X) = blockMat m * lin X`.
* `map_res_stable`: the image under `res` of a `(𝔤𝔩_n(ℂ), U(n))`-stable subspace `W` is
  `(𝔤𝔩_2(ℂ), U(2))`-stable. General elements of `ℂ ⊗[ℝ] 𝔤𝔩_2(ℂ)` are handled by induction on
  tensors, with `c ⊗ X = c • (1 ⊗ X)`.

## The rank-one Jacquet functionals

Assume `hre : 0 ≤ Re(t_d - t_e)`. Then also `0 ≤ Re(t_{d'} - t_{e'})` (`twist_exponent_sub`,
`re_twist_nonneg`).

* `lamN p hp pre post d e hpre hn hre c` is the rank-one Jacquet functional
  `ComplexSwapJacquet.functional` of `X_n(ds)` at the positions `p`, `p + 1`:
  `Λ_c^{(n)}(f) = ∫_ℂ (R(c E_{p+1,p+1}) f - κ_{p+1}(c) f)(s x(z)) dz`.
* `lamTwo d e s hre c` is the same functional `Λ_c^{(2)}` of `X_2([twist s d, twist s e])` at
  the positions `0`, `1`.
* `kappa_block`: `κ_1(c)` for `[d', e']` on `GL_2` equals `κ_{p+1}(c)` for `ds` on `GL_n`, since
  `2(t_e + s) + (2 - 1) - 2 = 2 t_e + (n - 1) - 2(p + 1)`.
* `integrand_res` and `lamTwo_res`: **the functional only sees the block**,
  `Λ_c^{(2)}(res f) = Λ_c^{(n)}(f)`. The two integrands agree pointwise:
  `R(c E_11)(res f)(chart z) = R(lin (c E_11)) f (block (chart z)) = R(c E_{p+1,p+1}) f (chart z)`,
  by `rightDerivative_restrictLin`, `lin_single` and `block_chart`, and `kappa_block` matches the
  constants.
* `exists_lamTwo_ne_zero`: if `(l_d, t_d) ≠ (l_e, t_e)`, then `Λ_c^{(2)} ≠ 0` for some `c`. This
  is `ComplexSwapJacquet.exists_integral_integrand_ne_zero` for `n = 2` and `pre = post = []`,
  applied to `twist s d`, `twist s e`. Twisting does not change the weights or the difference
  of the exponents.
* `isJacquet_lamN`: `Λ_c^{(n)}` is a Jacquet functional on `X_n(ds)` with the exponents
  `listExponent n es hes` and `listWeight n es hes` of `es = pre ++ e :: d :: post`. This is
  `ComplexSwapJacquet.isComplexJacquetFunctional_functional`, with the same list bookkeeping as
  `ComplexSwapJacquet.exists_swapJacquetFunctional`, for this particular functional.

## Linkage

* `isComplexLinked_symm`: `IsComplexLinked d e → IsComplexLinked e d`. The integers `p`, `q`
  are replaced by `-p`, `-q`.
* `isComplexLinked_twist_iff`: `twist s d` and `twist s e` are linked if and only if `d` and `e`
  are, because the differences `(t_d ± l_d/2) - (t_e ± l_e/2)` do not change.

## The key lemma

`eq_bot_of_lamN` takes `ComplexGLTwoUnlinkedIrreducibleStatement`, `¬ IsComplexLinked d e`, some
`c` with `Λ_c^{(2)} ≠ 0`, and a subspace `W` of `X_n(ds)` that is stable under `U(n)` and
`ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)` with `Λ_c^{(n)} = 0` on `W`. It concludes `W = ⊥`.

Proof. `V = res(W)` is `(𝔤𝔩_2(ℂ), U(2))`-stable (`map_res_stable`). `d'` and `e'` are not
linked (`isComplexLinked_twist_iff`), so `X_2([d', e'])` is irreducible and `V = ⊥` or `V = ⊤`.

* If `V = ⊤`, every `v` is `res w` with `w ∈ W`, so `Λ_c^{(2)}(v) = Λ_c^{(n)}(w) = 0`
  (`lamTwo_res`). This contradicts `Λ_c^{(2)} ≠ 0`.
* If `V = ⊥`, take `w ∈ W` and `k ∈ U(n)`. Then `ρ(k) w ∈ W`, so
  `(ρ(k) w)(1) = res(ρ(k) w)(1) = 0`. So `w = 0` by
  `ComplexPermutation.kFiniteEval_one_separating`.
