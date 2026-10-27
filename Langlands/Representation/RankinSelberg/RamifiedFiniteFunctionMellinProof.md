# Proof of uniform ramified Laurentness for scalar finite-function Mellin integrals

The module
`Langlands.Representation.RankinSelberg.RamifiedFiniteFunctionMellinProof`
proves

```text
theorem Langlands.RankinSelberg.ramifiedFiniteFunctionMellin :
    RamifiedFiniteFunctionMellinStatement.{uF}
```

for an arbitrary field universe `uF`. The target is the published
proposition in
`Langlands.Representation.RankinSelberg.RamifiedFiniteFunctionMellinStatement`.
It is imported by Lean name, and neither it nor anything it imports is
changed. The theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The theorem is the module's only public declaration. Every auxiliary
result defined here is `private`; continuity of the order is reused from
[DeterminantSlices](DeterminantSlices.md). The ordinary scalar Mellin work (Workers 352
and 656) owns its own growth and shell interfaces. These lemmas are shaped
for the ramified argument and add no competing public API.

## Auxiliary results

### Translation operators on finite functions

This part works on an arbitrary monoid `G`. Topological hypotheses are added
where needed.

- `eq_one_of_forall_norm_pow_sub_one_le` says that a complex normed ring has
  no small subgroups: if `‖g ^ n - 1‖ ≤ ε < 1` for every `n`, then `g = 1`.
  The proof uses the identity
  `n • (g - 1) = (g ^ n - 1) - ∑_{k<n} (g ^ k - 1) * (g - 1)`.
  It gives `n ‖g - 1‖ ≤ ε + n ε ‖g - 1‖`, which fails for large `n` unless
  `g = 1`.
- `translationSpan η` is the complex span of the left translates
  `a ↦ η (b * a)`. Its finite-dimensionality is exactly the statement's
  hypothesis. `translationOperator η u` is left translation by `u`,
  restricted to this span. It satisfies `T(u * w) = T(w) * T(u)` and
  `T(u ^ n) = T(u) ^ n`.
- In coordinates (`Module.finBasis`), `coordOperator η u` is a continuous
  linear map on `Fin d → ℂ`. Every vector in the span of a continuous `η` is
  continuous, so `u ↦ coordOperator η u` is continuous.
- `exists_nhds_translation_invariant`: the set
  `W = {u | ‖coordOperator η u - 1‖ < 1/2}` is a neighborhood of one. If
  every power of `u` lies in `W`, the no-small-subgroups lemma gives
  `coordOperator η u = 1`, so `η (u * a) = η a` for all `a`.
- `exists_translation_pow_bound`: for an element `g` and a compact set `K`,
  there are `C, r ≥ 0` with `‖η (g ^ n * a)‖ ≤ C * r ^ n` for all `n` and all
  `a ∈ K`. Here `r` is the operator norm of `coordOperator η g`. The bound `C`
  combines the coordinate norm of `η` with bounds on `K` for the basis
  vectors.

### Finite shell sums (`OrderShell`)

First come `ord_one`, `ord_inv`, `ord_pow` and `ord_zpow` for a map
`ord : G → ℤ` turning products into sums. The main lemma is
`exists_integral_eq_shell_sum`. Its setting is a measurable group `G` with
a left-invariant measure `μ`, a continuous `ord`, an element `ϖ` with
`ord ϖ = 1`, and an order-zero shell `{ord = 0}` of finite mass. Let `g` be
a continuous complex function with three properties:

- it vanishes where `ord < R0`;
- it satisfies `‖g (ϖ ^ j * k)‖ ≤ C * r ^ j` whenever `ord k = R0`;
- it satisfies `g (u * a) = c * g a` whenever `ord a ≥ N`, for some `u` with
  `ord u = 0` and some `c ≠ 1`.

Then there is `ρ > 0` such that for every `z` with `0 < ‖z‖ < ρ` the function
`a ↦ g a * z ^ ord a` is integrable, and its integral is
`∑_{n ∈ [R0, N)} (∫_{ord = n} g) * z ^ n`.

The proof runs as follows.

1. The shells `S n = {ord = n}` are measurable, because `ord` is
   continuous into the discrete group `ℤ`.
2. Left translation by `ϖ ^ (-n)` shows that every shell has the mass of
   `S 0`, which is finite.
3. On `S (R0 + j)` the growth hypothesis gives `‖g‖ ≤ C * r ^ j`. Below
   `R0` the function vanishes.
4. For `n ≥ N`, translation by `u` preserves `S n`. Left invariance
   (`integral_mul_left_eq_self`) then gives
   `∫_{S n} g = c * ∫_{S n} g`, so this shell integral is zero because
   `c ≠ 1`.
5. Take `ρ = 1 / (r + 1)`. Then `r ‖z‖ < 1`, and the shell norm integrals
   are bounded by a geometric series. This yields integrability through
   `integrableOn_iUnion_of_summable_integral_norm`.
6. The integral is the sum of the shell integrals (`integral_iUnion`). Only
   the shells with orders in `[R0, N)` contribute.

This abstract lemma uses no compactness: the growth hypothesis bounds every
shell.

### Local-field and spectral facts

- `localField_t2'`: a nonarchimedean local field is Hausdorff.
- The existing `continuous_ord_units` from `DeterminantSlices` gives
  continuity, hence local constancy, of `a ↦ T.ord a` on `F.Carrierˣ`.
- `discreteValuation_units`:
  `T.discreteValuation a = WithZero.exp (-T.ord a)` on units.
- `ord_eq_zero_iff_mem_integralUnits`: the order-zero units are the
  integral units. The proof compares `T.normalizedAbs` with one.
- `natCast_zpow_cpow_eq`:
  `((q ^ (-k) : ℝ) : ℂ) ^ (m * s) = (spectralPoint q s ^ m) ^ k`. The
  branch is fixed by `arg q = 0`.
- `spectralPoint_ne_zero'` and `exists_re_threshold`: for `1 < q` and
  `0 < m`, `‖spectralPoint q s ^ m‖ < ρ` whenever
  `Re s > -log (min ρ 1) / log q`.
- `eval_laurentToRatFunc_sum`: at a point `w ≠ 0`, evaluating
  `laurentToRatFunc (∑ C (d n) * T (e n))` gives `∑ d n * w ^ e n`.

## Main proof

1. The proof installs exactly the instances of the statement:
   `T.topology`, `T.valuativeRel`, `T.localField`, and the Borel structures
   on `F.Carrier` and `F.Carrierˣ`. It then takes continuity and
   finite-dimensionality of the translation span of `η`.
2. **Choice of `b`.** `exists_nhds_translation_invariant` gives a
   neighborhood `W` of one. `T.exists_principalUnits_subset` gives `b` with
   `T.principalUnits b ⊆ W`. This subgroup contains every power of each of
   its elements, so `η (u * a) = η a` for all `u ∈ T.principalUnits b`. The
   level `b` is chosen from `p`, `F`, `T` and `η` alone, before `α`, `m` and
   `Φ` are introduced.
3. **Data for fixed `α`, `m`, `Φ`.**
   - Fix `u ∈ T.principalUnits b` with `α u ≠ 1`. Let `ord a = T.ord a` on
     units; it is additive (`T.ord_mul`) and continuous.
   - Let `ϖ = LocalFactor.PadicAbelian.uniformizerUnit T`, so `ord ϖ = 1`.
     Also `ord u = 0`, because principal units have discrete valuation one.
   - The order-zero shell equals `integralUnits` of the valuation integer
     ring. It is compact (`integralUnits_isCompact`) and has mass one for
     the normalized Haar measure (`localMultiplicativeHaar_integerUnits`).
4. **The twisted function.** Let `g a = Φ a * η a * α a`. It is continuous.
5. **Lower order bound.** `T.normalizedAbs` is bounded by some `M` on the
   compact `tsupport Φ`. Choose `k` with `M < q ^ k`. If `ord a < -k`, then
   `T.normalizedAbs a = q ^ (-ord a) > M`, so `Φ a = 0`. Take `R0 = -k`.
6. **Growth.** The shell `{ord = R0}` is compact, as the image of the
   order-zero shell under multiplication by `ϖ ^ R0`. Several bounds
   combine on this shell:
   - `exists_translation_pow_bound`, applied to `η`, `ϖ` and this shell,
     bounds the translates of `η`;
   - `|Φ|` is bounded globally;
   - `α` is bounded on the shell;
   - `α (ϖ ^ j * k) = α ϖ ^ j * α k`.

   Together these give `‖g (ϖ ^ j * k)‖ ≤ C' * (r_η * ‖α ϖ‖) ^ j`.
7. **Ramified tail.** `Φ` is locally constant, so `Φ⁻¹ {Φ 0}` is a
   neighborhood of zero. `T.exists_additiveLattice_subset` places an
   additive lattice inside it. Hence `Φ a = Φ 0` whenever `ord a ≥ -k'`.
   The same holds for `u * a`, since `ord u = 0`. With `η (u * a) = η a`
   and multiplicativity of `α`, this gives `g (u * a) = α u * g a` for
   `ord a ≥ N = -k'`. Moreover `(α u : ℂ) ≠ 1`.
8. **Shell sum.** `exists_integral_eq_shell_sum`, with
   `μ = localMultiplicativeHaar F.Carrier`, gives a radius `ρ`.
9. **Spectral variable.** By `T.normalizedAbs_of_ne_zero` and
   `natCast_zpow_cpow_eq`, the integrand is
   `f s a = g a * (spectralPoint q s ^ m) ^ ord a`, where
   `q = T.residueCardinality`. `exists_re_threshold` gives `c0` with
   `‖spectralPoint q s ^ m‖ < ρ` for `Re s > c0`, and the spectral point is
   never zero.
10. **Conclusions.**
    - Integrability holds on `Re s > c0`.
    - Let `d n = ∫_{ord = n} g`. The Laurent coefficients are
      `L = ∑_{n ∈ [R0, N)} C (d n) * T (m * n)`.
    - `HasRationalContinuation q mellin (laurentToRatFunc L)` holds with the
      same bound `c0`. Regularity at the nonzero spectral point is
      `regularAt_laurentToRatFunc`. The identity is
      `mellin s = ∑ d n * (spectralPoint q s ^ m) ^ n`, which equals the
      evaluation by `eval_laurentToRatFunc_sum` and `zpow_mul`.

Positive weights `m`, including multiples of `p`, only replace the formal
variable `X` by `X ^ m`. Exponents `m * n` with `n < 0` are allowed in the
Laurent polynomial. Nothing restricts `α` to be unitary, and `Φ` may be
nonzero at zero.

## Sources and route

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
  *Rankin-Selberg Convolutions*, Amer. J. Math. **105** (1983), 367–464
  (`jpss-1983-rankin-selberg`).
  - Printed p. 392, displays (5)–(6): reduction to scalar integrals
    `∫ Φ_i(a) η_i(a) |a|^{is} d^×a`, which converge for large `Re(s)`.
  - Printed p. 404, proof of Proposition (2.13): when each `μ η_i` is
    ramified, each such integral is a polynomial in `q^s` and `q^{-s}`.
- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms
  on GL(3) I*, Ann. of Math. **109** (1979) (`jps-1979-gl3-i`), printed
  p. 181: the definition of a finite function.

The Lean proof implements the scalar mechanism behind Proposition (2.13).
It makes the uniformity explicit and does not use any other result from
those papers. Three steps differ in detail from the sources:

- Unit invariance of `η` comes from the no-small-subgroups argument for the
  continuous translation operators in coordinates. The proof does not cite
  the structure of finite functions.
- Absolute convergence comes from geometric growth of translates along
  powers of the uniformizer, rather than from an explicit expansion of `η`.
- Ramified cancellation is carried out shell by shell through left
  invariance of the normalized Haar measure.

The proof does not use L multiplicativity, section 9.3 tail divisibility,
or high-ramification L-vanishing.

Worker 235 wrote this module. No other worker's draft was reused.
