# Compact real matrix groups are cut out by polynomials (Chevalley)

This helper module proves a form of Chevalley's theorem that a compact subgroup of
`GL_n(ℝ)` is real algebraic. It is pure matrix analysis and does not mention schemes.

Polynomials are elements of `MvPolynomial (Coordinate n) ℝ`, where
`Langlands.GroupScheme.GeneralLinear.Coordinate n` has one variable for each matrix entry
(`.entry i j`) and one for each entry of the inverse (`.inverseEntry i j`). A matrix
`g : GL n ℝ` is evaluated through `values g : Coordinate n → ℝ`. This is the coordinate
format of `GeneralLinear` and of `IsPolynomiallyDefined`.

## Main result

`Langlands.Group.CompactMatrixZariski.exists_polynomial_separating`: let `C` be a subgroup
of `GL n ℝ` that is compact in the units topology, and let `g ∉ C`. Then there is a
polynomial `p` with `eval (values c) p = 0` for every `c ∈ C` and `eval (values g) p ≠ 0`.

Equivalently, `C` is the common zero set in `GL n ℝ` of the polynomials vanishing on it.

## Proof

1. `C` and `gC` are disjoint compact subsets of `GL n ℝ`. Their images under the injective
   continuous map `values` (`values_injective`, `continuous_values`) are disjoint compact
   subsets of `Coordinate n → ℝ`. Urysohn's lemma
   (`exists_continuous_zero_one_of_isClosed`) gives a continuous function equal to `0` on the
   first and `1` on the second. The Stone–Weierstrass theorem
   (`ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints`, for the
   subalgebra of polynomial functions, which separates points because the coordinates do)
   gives a polynomial `q` with `|q| < 1/4` on `C` and `|q - 1| < 1/4` on `gC`
   (`exists_polynomial_near_zero_one`).
2. Average the right translates of `q` over `C` with its normalized Haar measure `μ`
   (`Measure.haarMeasure` of the whole compact group, total mass `1`). The function
   `x ↦ ∫ q(x k) dμ(k)` is again a polynomial: `rightTranslation q` writes `q(x k)` as a
   polynomial in the coordinates of `x` whose coefficients are polynomials in those of `k`,
   and `average μ φ q` integrates each coefficient (`eval_average`).
3. For `c ∈ C`, the substitution `k ↦ c k` in `∫ q(c k) dμ(k)` uses left invariance of the
   Haar measure `μ` (`integral_mul_left_eq_self`): `∫ q(c k) dμ(k) = ∫ q(k) dμ(k)`. So the
   average of right translates is constant on `C`, equal to `κ = ∫ q(k) dμ(k)`. At `g`, the
   average minus `κ` is `∫ (q(g k) - q(k)) dμ(k) ≥ 1/2 > 0`, since `g k ∈ gC` and `k ∈ C`. So
   `p = average - κ` works.

## Auxiliary declarations

- `rightTranslationVar`, `rightTranslation`, `eval₂_rightTranslationVar`,
  `eval₂_rightTranslation`: the right translate `x ↦ q(x c)` as a polynomial in `x` with
  polynomial coefficients in `c` (inverse entries use `(x c)⁻¹ = c⁻¹ x⁻¹`).
- `average`, `eval_average`, `continuous_values`: averaging over a compact space with a finite
  measure along a continuous map into `GL n ℝ`.
- `finite_coordinate`, `coordinateFunction`, `aeval_coordinateFunction_apply`,
  `values_injective`, `exists_polynomial_near_zero_one`: the approximation step.
- `leftTranslationVar`, `leftTranslate`, `eval_leftTranslate`: for any field `k` and
  `a : GL n k`, the polynomial `leftTranslate a p` satisfies
  `eval (values x) (leftTranslate a p) = eval (values (a * x)) p`. It is used in
  `Langlands.GroupScheme.Rational.FiniteIndexPolynomialVanishing`.

## Provenance (derived)

The result is the key step of Borel–Tits, *Groupes réductifs* (1965), 14.3, printed p.146
(registered as `borel-tits-1965-groupes-reductifs`), which uses Chevalley's theorem that a
compact subgroup of `GL(n, ℝ)` is the group of real points of an algebraic group. Borel–Tits
cite that theorem without proof. The proof above (Stone–Weierstrass approximation followed
by Haar averaging) was written for this module and is not taken from a specific source. The
module states only the separation property above, not the full algebraicity theorem.
