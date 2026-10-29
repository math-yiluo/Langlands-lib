# Square-summability of square-integrable Whittaker functions on the torus lattice

Author: Worker 906. The helper modules credit further authors of reused code.

`Langlands.RankinSelberg.squareIntegrableWhittakerTorusSum` proves the published
statement

```lean
theorem squareIntegrableWhittakerTorusSum :
    SquareIntegrableWhittakerTorusSumStatement.{uF, uV}
```

with both universes independent. For an irreducible square-integrable representation `π`
of `G = GL_(m+1)(F)`, every Whittaker function `W` of the coefficient model and every
uniformizing `ϖ`, the family `δ(ϖ^μ)⁻¹ ‖W(ϖ^μ)‖²`, with `μ = (lam, 0)`, is summable over
`lam ∈ ℤ^m`. Here `δ(a) = ∏_{i<j} |a_i / a_j|` for the normalized absolute value.

The statement Markdown cites Jacquet, Piatetski-Shapiro and Shalika 1983, §8.3, which uses
this square-summability without proof. The proof here does not use the Whittaker asymptotic
expansion or an exponent criterion. It compares Whittaker functions directly with matrix
coefficients, a route the task contract allows. This route is internal to the project. The
irreducibility hypothesis is not used; only square-integrability modulo the centre (with the
admissibility it contains) is used.

The proof uses two helper modules:

- [`SquareIntegrableWhittakerTorusSumCoefficient`](SquareIntegrableWhittakerTorusSumCoefficient.md):
  on the antitone torus cone, a Whittaker function agrees with a smooth matrix coefficient
  that is invariant under a principal level `K(r)`.
- [`SquareIntegrableWhittakerTorusSumCells`](SquareIntegrableWhittakerTorusSumCells.md):
  square-integrability modulo the centre of such a coefficient makes its values on the
  antitone cone square-summable against `δ⁻¹`.

## Modulus lemmas

In the namespace `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum`:

- `torusModulus T ϖ e = ∏_{i<j} |ϖ^(e_i) / ϖ^(e_j)|`, which is literally the product in
  the statement.
- `normalizedAbs_zpow`: `|a^d| = |a|^d` for a unit `a` and `d ∈ ℤ`.
- `torusModulus_add`: `torusModulus T ϖ (e + e') = torusModulus T ϖ e * torusModulus T ϖ e'`.
- `torusModulus_pos`: the modulus is positive.

## Proof of the theorem

Let `W = f.val.val`. Square-integrability gives admissibility, hence smoothness of `π`. By
`modelMap_surjective`, `W(g) = ℓ (π(g) v)` for some vector `v`.

1. **Support.** `Whittaker.smoothSimpleRootSupport` gives `R` such that
   `W(diag(a)) ≠ 0` implies `|a_i / a_(i+1)| ≤ R` for every `i < m`. Apply it to
   `a = (ϖ^(e_i))_i` and the integral element `1`. Since `ϖ` is uniformizing,
   `0 < |ϖ| < 1`. The bound `|ϖ| ≤ 1` comes from `normalizedAbs_le_one_iff_mem_integers`.
   The inequality `|ϖ| ≠ 1` comes from `normalizedAbs_eq_one_iff_valuation_eq_one`. Choose
   `n` with `R < |ϖ|^(-n)`. If `W(ϖ^e) ≠ 0`, then `|ϖ|^(e_i - e_(i+1)) ≤ R`, which forces
   `e_i - e_(i+1) > -n` for every `i < m`.

2. **Shift.** Put `σ_i = n (m - i)`, so `σ_last = 0` and `σ_i - σ_(i+1) = n`. Let `σ'` be
   the restriction of `σ` to the first `m` coordinates. Then `(lam + σ', 0) = (lam, 0) + σ`.
   If `W(ϖ^(lam,0)) ≠ 0`, then `(lam + σ', 0)` is antitone, by `Fin.antitone_iff_succ_le`.

3. **Matrix coefficient.** Put `v' = π(ϖ^(-σ)) v`. Then `W(ϖ^e) = ℓ (π(ϖ^(e+σ)) v')` by
   `torus_add`. `exists_smooth_eq_on_antitone`, applied to `v'`, gives `r > 0` and a smooth
   functional `L`. The level `K(r)` fixes `v'`, `L` is `K(r)`-invariant, and
   `L (π(ϖ^e) v') = ℓ (π(ϖ^e) v')` for antitone `e`.

4. **Square-integrability.** Give `G / Z` its Borel structure, and take a Haar measure `μ`
   from `exists_isHaarMeasure_centralQuotient`. `T.IsSquareIntegrable π` at `μ` gives a
   unitary central character `c` with `c.coefficientNorm L v'` in `L²(μ)`. Here `L` is used
   as an element of `SmoothDual π`. `summable_antitone` then gives summability of
   `δ(ϖ^(lam,0))⁻¹ ‖L (π(ϖ^(lam,0)) v')‖²` over the `lam` with `(lam, 0)` antitone.

5. **Transport.** The map `j(lam) = lam - σ'` from the antitone cone to `ℤ^m` is injective.
   Outside its range, `(lam + σ', 0)` is not antitone, so `W(ϖ^(lam,0)) = 0` by step 2 and
   the summand vanishes. By `Function.Injective.summable_iff`, it suffices to sum along `j`.
   For `lam` in the cone, put `e = (j lam, 0)`, so `e + σ = (lam, 0)`. Then
   `W(ϖ^e) = L (π(ϖ^(lam,0)) v')` by steps 3 and 2. Also
   `δ(ϖ^e)⁻¹ = δ(ϖ^σ) δ(ϖ^(lam,0))⁻¹` by `torusModulus_add` and positivity. So the summand
   at `j lam` is the constant `δ(ϖ^σ)` times the summable family of step 4.
