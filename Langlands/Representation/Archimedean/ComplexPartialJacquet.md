# The partial Jacquet integral of `GL_{m+1}(ℂ)` along `P_{m,1}`

Lean module: `Langlands.Representation.Archimedean.ComplexPartialJacquet`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the complex counterpart of Worker 5220's module
`PartialJacquetIntegral` for `GL_n(ℝ)` (Task 6749), and follows its proof.

For a function `h` of the principal series of `GL_{m+1}(ℂ)` the module defines the partial
Jacquet integral

`T h(g) = ∫_{ℂ^m} h(J(x,1) ι(g)) dx`,  `g ∈ GL_m(ℂ)`  (`jacquetStep`),

where `J(x,1)` is the identity matrix with last row `(x, 1)` (`chartGL`), `ι(g) = diag(g, 1)`
(`iotaGL`) and `dx` is Lebesgue measure on `ℂ^m`. This is the integral over the opposite
unipotent radical `N̄_P` in induction in stages through the maximal parabolic subgroup `P_{m,1}`.
The main statement is `Langlands.Archimedean.ComplexPartialJacquetStatement`, proved as
`Langlands.Archimedean.complexPartialJacquet`. In the proof of the Langlands quotient theorem the
integral is iterated to a nonzero linear functional on the standard module that vanishes on every
proper `(g, K)`-submodule.

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n` (or
`Matrix.unitaryGroup (Fin n) ℂ`, included by `Unitary.toUnits`). `principalSeries`,
`principalSeriesCharacter`, `kFiniteFunctions` and `Whittaker.rightTranslation` are the Library's.
`chartGL`, `iotaGL`, `dlastGL` (`d(s) = diag(1, …, 1, s)`) and `Jmat` come from
`ComplexMaximalParabolicIntegration`; `partialSq`, `norm_le_chart`,
`integrable_prod_one_add_sq_rpow` and `prod_partialSq_rpow_le` from `ComplexParabolicChartBound`;
`phaseUnit z = z/|z|` from `ComplexGramFormula`; `phaseMatrix` and `extension_mem_kFiniteFunctions`
from `ComplexPrincipalSeriesExtension`. Declarations without a prefix are in the namespace
`Langlands.Archimedean.ComplexPartialJacquet`.

## The statement

`ComplexPartialJacquetStatement`: let `χ_l : ℂˣ → ℂ` (`l ∈ ℕ`) and `e : ℕ → ℂ` satisfy

* `χ_l(z) = χ_l(z/|z|) · (|z|²)^{e_l}` for all `l` and `z`,
* `χ_l(1) = 1` and `|χ_l(z/|z|)| = 1`, and
* `Re e_{l+1} < Re e_l` for every `l < m`.

Let `h` be a `U(m+1)`-finite function of the smooth principal series of `χ` on `GL_{m+1}(ℂ)`.
Then `x ↦ h(J(x,1) κ)` is integrable on `ℂ^m` for every `κ ∈ U(m+1)`, and
`g ↦ ∫_{ℂ^m} h(J(x,1) ι(g)) dx` is a `U(m)`-finite function of the smooth principal series of the
characters `χ_l(z) (|z|²)^{-1/2}` on `GL_m(ℂ)`.

Provenance. Derived, internal infrastructure. That the integral over `N̄_P` of a function of
`Ind_B^G χ` converges for strictly dominant `χ` and lands in the principal series of the Levi
factor, with the shift by `δ_P^{1/2}`, is the standard computation of induction in stages and of
the Jacquet integral (convergence: the chart bound below). No literature claim beyond this.

## Characters

* `IsPhasePower χ e` (structure) collects the three conditions on the characters at every
  position `l`: `χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}` (the hypothesis of the extension lemma),
  `χ_l(1) = 1` and `|χ_l(z/|z|)| = 1`. Consequences: `|χ_l(z)| = |z|^{2 Re e_l}`
  (`IsPhasePower.norm`) and `χ_l(z) ≠ 0` (`IsPhasePower.ne_zero`).
* `dualChar χ = χ⁻¹` is a phase power with exponents `−e` (`IsPhasePower.dual`).
  `shiftChar χ = χ (|·|²)^{−1/2}` is a phase power with exponents `e − 1/2`
  (`IsPhasePower.shift`).
* `IsStrictlyDominant e m`: `Re e_{l+1} < Re e_l` for every `l < m`, i.e. for the positions
  `0, …, m` of `GL_{m+1}`. It passes to the shifted exponents on `GL_m`
  (`IsStrictlyDominant.shift`).
* `normExponent e N l = 2 (Re e_l + (N−1)/2 − l)` is the exponent of `|χ δ^{1/2}|`
  (`norm_principalSeriesCharacter`: `|principalSeriesCharacter ℂ N χ a| = ∏ |a_l|^{normExponent}`).
  `chartExponent e l = Re e_{l+1} − Re e_l − 1` is the exponent of the chart bound; it is `< −1`
  under strict dominance (`chartExponent_lt`).

## Chart identities and changes of variables

* `chartGL_mul_iotaGL`: `J(x,1) ι(g) = ι(g) J(x g, 1)`.
* `chartGL_mul_dlastGL`: `J(x,1) d(s) = d(s) J(s⁻¹x, 1)`.
* `chartGL_mul_chartGL_neg`: `J(x,1) J(−x,1) = 1`.
* `chartGL` and `iotaGL` are continuous (`continuous_chartGL`, `continuous_iotaGL`).
* For an invertible complex matrix `B`, `x ↦ x B` is a linear equivalence of `ℂ^m`
  (`vecMulLinearEquiv`, determinant `det B` by `det_vecMulLinearEquiv`) and a measurable
  equivalence (`vecMulEquiv`). As a real-linear map its determinant is `|det B|²`
  (`LinearMap.det_restrictScalars` and `Algebra.norm_complex_apply`), so Lebesgue measure
  transforms by `|det B|^{−2}` (`map_vecMulEquiv`, from `Measure.map_linearMap_addHaar_eq_smul_addHaar`).
  This gives `integral_vecMul_smul`, `integral_vecMul_eq` (`∫ f(x B) dx = |det B|^{−2} ∫ f`) and
  `integrable_comp_vecMul`.

## Bounds and convergence

* `norm_le_partialSq`: for `h` in the principal series of a phase power `χ` with `|h| ≤ C` on
  `U(m+1)`, `|h(J(x,1)κ)| ≤ C ∏_{l<m} r_{l+1}(x)^{chartExponent e l}` for `κ ∈ U(m+1)`, where
  `r_l(x) = 1 + ∑_{j<l} |x_j|²`. This is `ComplexParabolicChartBound.norm_le_chart` with
  `σ = normExponent e (m+1)`.
* `norm_le_of_mem_principalSeries`: under strict dominance the exponents are negative, so
  `|h(J(x,1)κ)| ≤ C ∏_l (1 + |x_l|²)^{chartExponent e l}`. Since every exponent is `< −1`, this
  bound is integrable on `ℂ^m`, so `x ↦ h(J(x,1)κ)` is integrable (`integrable_chart`).
  (`exists_bound_unitaryCompact` gives `C` by compactness of `U(m+1)`.)
* `continuous_jacquetStep_unitary`: `κ ↦ T h(κ)` is continuous on `U(m)`, by
  `continuous_of_dominated` with the bound above, which does not depend on `κ` because `ι(κ)` is
  unitary.

## Equivariance and finiteness

* `principalSeriesCharacter_lastCases`: if `χ_m(1) = 1`, then
  `(χ δ^{1/2})_{m+1}(a, 1) · (∏_i |a_i|²)^{−1} = (shiftChar χ) δ^{1/2}_m(a)` for `a ∈ (ℂˣ)^m`.
* `jacquetStep_mul`: `T h(diag(a) u g) = principalSeriesCharacter ℂ m (shiftChar χ) a · T h(g)`
  for `u` upper unipotent. Write `b = diag(a) u`. Then `J(x,1) ι(b g) = ι(b) J(x b, 1) ι(g)`,
  `ι(b) = diag(a, 1) ι(u)` with `ι(u)` upper unipotent, and the substitution `x ↦ x b` contributes
  `|det b|^{−2} = ∏_i |a_i|^{−2}`.
* `jacquetStep_rightTranslation`: `T(R(ι(k)) f)(g) = T f(g k)`.
* `jacquetStepOn` is `T` followed by restriction to `U(m)`, as a linear map on a subspace of the
  principal series (additivity uses `integrable_chart`). `finiteDimensional_jacquetStep`: the
  right translates of `κ ↦ T h(κ)` by `U(m)` lie in the image under `jacquetStepOn` of the span of
  the right translates of `h` by `U(m+1)`, which is finite-dimensional because `h` is
  `U(m+1)`-finite.

## The main result

`jacquetStep_mem`: let `χ` be a phase power with `IsStrictlyDominant e m`, and let `h` be a
`U(m+1)`-finite function of the principal series of `χ`. Then `T h` is a `U(m)`-finite function of
the principal series of `shiftChar χ`. Proof:

* `φ(κ) = T h(κ)` on `U(m)` is continuous and `U(m)`-finite (above).
* `φ(phaseMatrix a · κ) = principalSeriesCharacter ℂ m (shiftChar χ) (a/|a|) · φ(κ)`, by
  `phaseMatrix_toUnits` (`phaseMatrix a = diag(a/|a|)` with trivial unipotent part) and
  `jacquetStep_mul`.
* `ComplexPrincipalSeriesExtension.extension_mem_kFiniteFunctions` (with exponents `e − 1/2` and
  `IsPhasePower.shift`) gives an element `E` of the `U(m)`-finite principal series of
  `shiftChar χ` with `E = φ` on `U(m)`.
* `T h = E` on all of `GL_m(ℂ)`: write `g = diag(a) u k` with
  `ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary`. Both functions transform
  by the same character (`jacquetStep_mul`, and principal-series membership of `E`), and they agree
  at `k` (`extension_unitary`).

`complexPartialJacquet` assembles the statement from `integrable_chart` and `jacquetStep_mem`.
