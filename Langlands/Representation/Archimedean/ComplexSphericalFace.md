# Cyclicity of the spherical vector with tied blocks (nonincreasing real parts)

Lean module: `Langlands.Representation.Archimedean.ComplexSphericalFace`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. The operator (request
`08a6dcd43c545ecdb45b5e19f96ef9f4`) assigned the Library statement
`ComplexTemperedStandardIrreducibleStatement` (written U below) to Worker 728 (Task 7064), and
asked for supporting lemmas to be staged under Task 7063. This module is Worker 140's part "P2,
face case", agreed with Worker 728. It treats spherical vectors whose exponents have nonincreasing
real parts, not all equal. The strictly decreasing case alone is the module
`ComplexSphericalJacquet` (staged candidate `0c71bb5c-8ef2-47e1-a8c7-4d3b85aabd88`). This module
imports that one. The case of all real parts equal is Worker 728's part.

Notation: `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ` and `U(N)` is `unitaryCompact ℂ N` (the
image of `Matrix.unitaryGroup (Fin N) ℂ` under `Unitary.toUnits`). Characters are
`χ : ℕ → ℂˣ → ℂ` with exponents `e : ℕ → ℂ`. `IsPhasePower χ e` means
`χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1` and `|χ_l(z/|z|)| = 1`; `phaseUnit z = z/|z|`.
For `X ∈ M_{m×a}(ℂ)` (as `Fin m → Fin a → ℂ`), `n̄(X) = [[1, 0], [X, 1]] ∈ GL_{a+m}(ℂ)` is
`ComplexBlockParabolic.blockLowerGL`. `J(v, 1) = chartGL v` is the identity matrix with its last
row replaced by `(v, 1)`, and `ι(g) = diag(g, 1)` is `iotaGL`. `r_l(y) = partialSq y l =
1 + ∑_{j<l} |y_j|²`. `chartFun a s w y = r_a(y)^w ∏_{l<a} r_{l+1}(y)^{s_l}` and `TailCondition` are
those of `ComplexSphericalJacquet` and `ComplexPartialSqIntegral`. Block decompositions `ks` (last
block first, block sizes `k + 1`), `dim ks`, `BlockOrdered`, `blockStep`, `blockPair`,
`blockVector` and the block Jacquet functional `jac ks e p` are those of `ComplexBlockJacquet` and
`ComplexBlockFunctional`. In `IsBlockDominant e a k` the last block `a, …, a+k` is tied, the real
parts do not increase on `0, …, a`, and `Re e_a < Re e_{a-1}`. Unprefixed names below are in
`Langlands.Archimedean.ComplexSphericalFace`.

## The statement

`Langlands.Archimedean.ComplexSphericalFaceCyclicStatement`: for every `n` and every list `ds` of
`n` complex characters (`ComplexCharacterData`) such that

* `TemperedIrreducibleAt b` holds for every `b < n`
  (`ComplexBlockFunctionalSized.TemperedIrreducibleAt b`: the standard modules of all lists of `b`
  complex characters whose exponents have equal real parts are irreducible),
* every weight is `0`, so the `i`-th character is `z ↦ |z|^{2 t_i}` with `t_i = exponent`,
* the real parts of the exponents do not increase along the list
  (`ds.Pairwise (fun d e => e.exponent.re ≤ d.exponent.re)`), and
* two entries of `ds` have different real parts of their exponents,

and every `U(n)`-finite function `f₀` of `complexStandardModule n ds` with `f₀(κ) = 1` for all
`κ ∈ U(n)` (the spherical vector): every subspace `W` of the `U(n)`-finite functions of
`complexStandardModule n ds` that is stable under `complexStandardRep n ds k` for all `k ∈ U(n)`
and under `complexStandardLie n ds Z` for all `Z ∈ ℂ ⊗_ℝ M_n(ℂ)`, and contains `f₀`, is everything
(`W = ⊤`).

It is proved as `Langlands.Archimedean.complexSphericalFaceCyclic`. The block form
`Langlands.Archimedean.complexSphericalBlockCyclic` (a theorem with hypotheses) has the same
conclusion for `complexStandardModule (dim ks) ds` under three assumptions: an explicit block
decomposition `ks` with `BlockOrdered ks (complexPositionExponent ds)`, weights `0`, and
`TemperedIrreducibleAt (k + 1)` for every `k ∈ ks`.

The hypotheses on irreducibility are needed only at the block sizes. When the real parts are not
all equal, these sizes are less than `n`.

Provenance. Derived, internal infrastructure for the proof of U. The block integrals computed
here are Gindikin–Karpelevich-type integrals of the spherical function. The classical product
formula is not cited: the module proves only that the integrals are nonzero, by the route below.
No literature statement is claimed; the statement is exactly the Lean proposition above.

## Proof

### Masked Gram determinants

For `X ∈ M_{m×a}(ℂ)`:

* `maskC l X` replaces the columns `≥ l` by `0`, and `maskR j X` the rows `< j`.
* `gramC Y = det(1 + Yᴴ Y)`, a positive real number (`gramC_pos`, by positive definiteness;
  `gramC_eq_re`, `gramC_re_pos`).
* `cG l X = D_l(X) = Re det(1 + X_{<l}ᴴ X_{<l})` (columns `< l`) and
  `rG j X = E_j(X) = Re det(1 + X^{(j)ᴴ} X^{(j)})` (rows `≥ j`).
  `cG_eq_rG_zero`: `D_a = E_0`. For `m = 0` all of them are `1` (`cG_zero_rows`, `rG_zero_rows`).
* `cG_cons_eq_snoc`: `D_l` does not depend on the order of the rows: prepending or appending a row
  `x` gives the same value. `rG_cons_succ`: `E_{j+1}` of `X` with the row `x` prepended is
  `E_j(X)`.
* `gram_blockLower_eq_cG`, `gram_blockLower_eq_rG`: the Gram determinants of the rows `≥ l` of
  `n̄(X)` (`ComplexGramFormula.gram`) are `D_l(X)` for `l ≤ a` and `E_j(X)` at `l = a + j`.
  The proof uses the Library's `gram_blockLower_le` and `gram_blockLower_ge`, the
  Weinstein–Aronszajn identity `det(1 + AB) = det(1 + BA)`, and the reindexing `sum_fromIdx`.

### The triangular change of variables

* `mul_apply_self_of_upper`, `diagonalTail_mul_of_upper`: diagonals of products of upper
  triangular matrices. `isUpperTriangular_iota`, `diagonalTail_iota`: the same for `ι`.
* `gram_iota_mul_chartGL`: for `b ∈ GL_N(ℂ)` upper triangular, `κ ∈ U(N)` and `l ≤ N`, the Gram
  determinant of the rows `≥ l` of `ι(b) J(w, 1) ι(κ)` is `|∏_{j ≥ l} b_{jj}|² · r_l(w)`.
  Proof: take the Iwasawa decomposition of `J(w, 1)`
  (`ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary`), then use
  `ComplexGramFormula.gram_mul_conj` and the Library's `prod_tail_sq_eq`.
* `blockLower_snoc`: `n̄(X; x) = J(v, 1) ι(n̄(X))` with `v = (x, 0) ∈ ℂ^{a+m}`, where `(X; x)` is `X`
  with the row `x` appended (an entrywise computation; `blockLower_castAdd_castAdd` etc.).
* `partialSq_append_vecMul`: for `l ≤ a`, `r_l((x, 0) B) = r_l(x M)`, where `M` is the top left
  `a × a` block of `B`.
* `exists_triangular`: for every `X ∈ M_{m×a}(ℂ)` there is `M` with `det M ≠ 0`,
  `|det M|⁻² = D_a(X)`, and `D_l(X; x) = D_l(X) · r_l(x M)` for all `x ∈ ℂ^a` and `l ≤ a`.
  Write `n̄(X) = b κ` (Iwasawa, `b` upper triangular) and let `M` be the top left block of `b`.
  Then `n̄(X; x) = ι(b) J((x, 0) b, 1) ι(κ)` (`blockLower_snoc`,
  `ComplexPartialJacquet.chartGL_mul_iotaGL`), and `gram_iota_mul_chartGL` gives the identity. The
  determinant: `M` is upper triangular with the first `a` diagonal entries of `b`. The Gram
  determinants of `n̄(X)` at `0` and `a` are `1` and `D_a(X)`, and they are the squared moduli
  of the products of all, respectively the last `m`, diagonal entries.

### The Gindikin–Karpelevich integral of a tied block

* `psi m s w t X = Ψ_m(s, w, t)(X) = D_a(X)^w ∏_{l<a} D_{l+1}(X)^{s_l} ∏_{1 ≤ j < m} E_j(X)^{t_j}`
  (complex powers of positive reals); `psi_zero`: `Ψ_0 = 1`.
* `psi_cons`: if `M` is as in `exists_triangular` for `X`, then `Ψ_{m+1}(s, w, t)(x; X)` (the row
  `x` prepended) is
  `D_a(X)^w ∏_l D_{l+1}(X)^{s_l} ∏_{j<m} E_j(X)^{t_{j+1}} · chartFun a s w (x M)`.
* `psi_merge`: that prefactor times `D_a(X)` is `Ψ_m(s, w + 1 + t_1, j ↦ t_{j+1})(X)`. For `m ≥ 1`
  this uses `E_0 = D_a`; for `m = 0` everything is `1`.
* `integral_psi_succ`: if `Ψ_{m+1}(s, w, t)` is integrable, then
  `∫ Ψ_{m+1}(s, w, t) = (∫ chartFun a s w) · ∫ Ψ_m(s, w + 1 + t_1, j ↦ t_{j+1})`.
  Proof: Fubini over `M_{(m+1)×a} = ℂ^a × M_{m×a}`, first row first
  (`volume_preserving_piFinSuccAbove`, `integral_prod_symm`). Then `psi_cons` and the linear
  change of variables `x ↦ x M` (`ComplexPartialJacquet.integral_vecMul_eq`, factor
  `|det M|⁻² = D_a(X)`), and `psi_merge`.
* `integral_psi_zero_rows`: `∫ Ψ_0 = 1`.
* `continuous_gramC`, `continuous_cG`, `continuous_rG`, `measurable_psi`, `norm_psi`.
* `norm_psi_eq_bound`: if `Re w = 0` and `Re t_j = -1` for `1 ≤ j ≤ k`, then
  `‖Ψ_{k+1}(s, w, t)(X)‖ = blockChartBound (Re s) X`. Here `D_{l+1} = colGram X l` and
  `E_{j+1} = rowGram X (j+1)`, via the Library's `gramRe_blockLower_col` and
  `gramRe_blockLower_row`.
* `integrable_psi`: under these conditions and `TailCondition (Re s) 0`, `Ψ_{k+1}(s, w, t)` is
  integrable (the Library's `complexBlockChartIntegrable`).
* `integral_psi_ne_zero`: if `TailCondition (Re s) 0`, `Re w = 0` and `Re t_j = -1` for
  `1 ≤ j < m`, then `∫ Ψ_m(s, w, t) ≠ 0`. Induction on `m` with `integral_psi_succ`. The factor
  `∫ chartFun a s w` is nonzero by `ComplexSphericalJacquet.integral_chartFun_ne_zero`. The new
  parameters satisfy the same conditions, because `Re(w + 1 + t_1) = 0`.

### The spherical vector along `n̄(X)`

Assume `IsPhasePower χ e` and `χ_l(z/|z|) = 1`, and let `T` be in the principal series of `χ` on
`GL_{a+k+1}(ℂ)` with `T(κ) = T(1)` on `U(a+k+1)`.

* `principalSeriesCharacter_blockLower`: if `n̄(X) = diag(z) u κ` (Iwasawa), then
  `principalSeriesCharacter ℂ (a+k+1) χ z = ∏_{l < a+k} G_{l+1}^{e_{l+1} - e_l - 1}`. Here `G_l`
  is the Gram determinant of the rows `≥ l` of `n̄(X)`. The proof is summation by parts
  (`ComplexSphericalJacquet.sum_mul_eq_sum_sub_complex`). It uses
  `G_l = |∏_{j ≥ l} z_j|²` (`ComplexBlockChart.prod_tail_sq_eq_gram`) and `G_0 = 1`.
* `apply_blockLower`: `T(n̄(X)) = T(1) Ψ_{k+1}(s, 0, t)(X)` with `s_l = e_{l+1} - e_l - 1` and
  `t_j = e_{a+j} - e_{a+j-1} - 1` (`gram_blockLower_eq_cG`, `gram_blockLower_eq_rG`).
* `blockStep_one`: `blockStep T 1 = T(1) ∫ Ψ_{k+1}(s, 0, t)`.
* `blockStep_one_ne_zero`: if moreover `IsBlockDominant e a k` and `T(1) ≠ 0`, then
  `blockStep T 1 ≠ 0`. `TailCondition (Re s) 0` is the Library's `tail_h`. The tie
  `Re e_{a+j} = Re e_a` for `j ≤ k` gives `Re t_j = -1`.

### The block Jacquet functional of the spherical vector

* `blockVector_zero_unitary`: with weights `0`, `blockVector a k e 0` is `1` on `U(k+1)`
  (`ComplexPrincipalSeriesExtension.extension_unitary`; the phase monomial with zero exponents
  is `1`).
* `blockPair_spherical`: for `κ₁ ∈ U(a)`, `blockPair (blockVector a k e 0) T κ₁ = blockStep T 1`.
  `blockStep T (diag(κ₁, κ₂)) = blockStep T 1` by right `U`-invariance
  (`ComplexSphericalJacquet.apply_mul_unitary`), and `unitaryHaar (k+1)` is a probability
  measure.
* `jac_ne_zero`: if `IsPhasePower χ e`, `χ_l(z/|z|) = 1`, `BlockOrdered ks e`, and `T` is a
  `U`-finite function of the principal series of `χ` on `GL_{dim ks}(ℂ)` with `T = T(1)` on `U` and
  `T(1) ≠ 0`, then `jac ks e 0 T ≠ 0`. Induction on `ks`: `jac [] e 0 T = T(1)`. For `k :: ks`, the
  paired function `blockPair (blockVector (dim ks) k e 0) T` has the following properties:
  * it is a `U`-finite function of the principal series of `blockShiftChar k χ`
    (`ComplexBlockJacquet.blockPair_mem` with `complexBlockChartIntegrable`);
  * it is trivial on phases;
  * it is constant on `U(dim ks)` with value `blockStep T 1 ≠ 0`.

  The exponents remain `BlockOrdered` after the shift (`BlockOrdered.shift`).

### Maximal runs, and the closed statements

* `exists_blocks`: let the real parts of `e_0, …, e_{n-1}` not increase. Then there is `ks` with
  `dim ks = n` and `BlockOrdered ks e`. Every block has size `≤ n`, and `< n` if two real parts
  differ. Proof: strong induction on `n`. The last block runs from the least index `a` with
  `Re e_a = Re e_{n-1}` to `n - 1`. The induction hypothesis at `a` gives the rest. The gap
  `Re e_a < Re e_{a-1}` holds by minimality of `a`. If two real parts differ, then `a > 0`.
* `complexPositionExponent_eq`: `complexPositionExponent ds l` is the exponent of `ds[l]`.
* `complexSphericalBlockCyclic`: suppose `W ≠ ⊤`. Its image in the function space is a proper
  subspace that is stable under `U` and the right derivatives (as in
  `complexSphericalCyclic`). So `complexBlockFunctionalSized` gives `jac ks e 0 f₀ = 0`. This
  contradicts `jac_ne_zero`: the characters `complexPositionCharacter ds` are phase powers
  (`ComplexStrictLanglandsQuotient.isPhasePower`), and they are trivial on phases because all
  weights are `0` (`ComplexSphericalJacquet.complexPositionWeight_eq_zero`).
* `complexSphericalFaceCyclic`: the list hypothesis gives nonincreasing real parts of
  `complexPositionExponent ds` on `0, …, n-1` (`List.pairwise_iff_getElem`). Apply `exists_blocks`;
  its blocks have sizes `< n`, so `TemperedIrreducibleAt (k + 1)` holds for each block. Then apply
  `complexSphericalBlockCyclic`.
