# Growth on functions that are polynomial along a lower root subgroup

Module `Langlands.Representation.Archimedean.RealRootPolynomialGrowth`, namespace
`Langlands.Archimedean.RootPolynomial`.

Notation: `G = GL_n(ℝ)`, `𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`, `U = U(𝔤)`, `U_d = degreeFiltration ℂ 𝔤 d`, `R(X)`
the right derivative. `c₀ = (a, b)` is a position with `b < a` (hypothesis `hc₀`). `I(ds)` is
the space of `O(n)`-finite functions of the real standard module `realStandardModule n ds`, with
the action `realStandardLie n ds`. The module uses `smoothLie`, `adU`, `rightTranslate`
(`RealSmoothRightAction`), `nbar`, `LowIdx` (`RealLowerUnipotentRestriction`) and `J`, `adMap`
(`RealLeftPolynomialCount`).

## Definitions

* `rootMatrix c₀ = E_{ab}`. `rootUnit hc₀ t` is `e(t) = 1 + t E_{ab}` in `G`, with inverse
  `1 - t E_{ab}` (because `E_{ab}² = 0`).
* `node k i = i` (for `i < k`, as a complex number) and `lag k i`, the Lagrange basis polynomials
  for these `k` nodes (`Lagrange.basis`).
* `IsRootPoly hc₀ k f`: for all real `t` and all `g ∈ G`,
  `f(e(t) g) = ∑_{i < k} (lag k i)(t) · f(e(i) g)`. In words, `t ↦ f(e(t) g)` is the polynomial of
  degree `< k` that interpolates its values at `t = 0, 1, …, k - 1`.
* `polySpace χ hc₀ k`: the functions `f ∈ principalSeries ℝ n χ` with `IsRootPoly hc₀ k f`, a
  complex subspace.

## Results

* `rootMatrix_mul_self`, `smul_rootMatrix_mul`, `rootUnit_val`, `rootUnit_zero`,
  `rootUnit_val_mul` (`e(t)(1 + s E) = e(t + s)`).
* `hasDerivAt_rootUnit`: for smooth `f`, `t ↦ f(e(t))` has derivative `(R(E) f)(e(t))` at `t`.
* `isRootPoly_of_polynomial`: if for every `g` there is a complex polynomial `q` of degree `< k`
  with `f(e(t) g) = q(t)` for all real `t`, then `IsRootPoly hc₀ k f`.
* `isRootPoly_rightTranslation`, `isRootPoly_rightDerivative` (for smooth `f`):
  `IsRootPoly` is preserved by right translations and right derivatives.
* `polySpace_smooth`, `rightDerivative_mem_polySpace`, `polySpace_le`,
  `envelopingAction_mem_polySpace`: `polySpace` consists of smooth functions and is stable under
  the action of `U` on smooth functions.
* `iterate_rightDerivative_apply_one`: if `f` is smooth and `IsRootPoly hc₀ k f`, then
  `(R(E)^k f)(1) = 0`.
* `exists_eigen`: there is `μ : Fin n × Fin n → ℂ` such that `(R(E_c) f)(1) = μ_c f(1)` for every
  upper position `c` and every `f ∈ principalSeries ℝ n χ`.
* `envelopingAction_gen_coe`, `envelopingAction_gen_pow_coe`: `gen c` acts on smooth functions
  by `R(E_c)`, and `gen c₀ ^ j` by `R(E)^j`.
* `eval_one_eq_zero_of_mem_J`: with such `μ`, for `w ∈ J μ c₀ k` and `f ∈ polySpace χ hc₀ k`,
  `(w · f)(1) = 0`.
* `finrank_map_le_of_ker`: if `P` is finite-dimensional and `Ψ x = 0` implies `T x = 0` on `P`,
  then `dim T(P) ≤ dim Ψ(P)`.
* `finrank_map_le_of_isRootPoly` (**main theorem**): let `Y` be a subspace of `I(ds)` with
  `IsRootPoly hc₀ k h` for every `h ∈ Y`. Then there is `C` such that for all `d`, the operators
  `h ↦ u h` from `Y` to `I(ds)`, `u ∈ U_d`, span a space of dimension at most
  `C (d + 1)^(n (n - 1) - 1)`. The proof gives `C = (n + 2)^N k`, with `N = n (n - 1) / 2`.

## Provenance

Internal to the proof of `RealLinkedLanglandsQuotientNotLargeStatement`. The main theorem is the
statement `RealLeftPolynomialGrowthStatement` (module `RealLeftPolynomialGrowth`) for an arbitrary lower position `c₀`, with the
polynomial condition in the form `IsRootPoly`. Its Markdown suggests a count of polynomial
differential operators in the noncompact picture (Knapp 1986, Chapter VII). The proof here is
the same count, carried out algebraically through `U(𝔤)`, and not taken from a source.
Evaluation at `1` is an eigenfunctional for the upper triangular Borel subalgebra on the
principal series. On functions that are polynomial along `e(t)`, it is also killed by `E^k`.
The value of `u h` at `n̄` is evaluation at `1` of `Ad(n̄) u` applied to `ρ(n̄) h`. So it only
depends on `Ad(n̄) u` modulo the right ideal `J`, and the count of `RealLeftPolynomialCount`
applies.

## Proofs

* `hasDerivAt_rootUnit`: let `ψ(y) = f̃(e(t) y)` on matrices, with `f̃ = unitsExtension f`. Its
  derivative at `1` applied to `E` is `(R(E) f)(e(t))` (Library
  `rightDerivative_eq_fderiv_mul_left`). Along the line `s ↦ 1 + s E`, `ψ(1 + s E) = f(e(t + s))`
  (`rootUnit_val_mul`). The chain rule gives the derivative of `s ↦ f(e(t + s))` at `0`. Shift by
  `t` (`HasDerivAt.comp_sub_const`).
* `isRootPoly_of_polynomial`: `q` equals its Lagrange interpolation at the `k` nodes
  (`Lagrange.eq_interpolate`), and `q(i) = f(e(i) g)`.
* `isRootPoly_rightDerivative`: `(R(X) f)(e(t) g) = R(X)(x ↦ f(e(t) x))(g)`
  (`rightDerivative_comp_mul_left`). By `IsRootPoly`, `x ↦ f(e(t) x)` is the combination
  `∑_i lag_i(t) · (x ↦ f(e(i) x))` of smooth functions. `R(X)` is linear on smooth functions
  (`rightDerivativeLinearMap`). Apply `rightDerivative_comp_mul_left` again to each term.
* `envelopingAction_mem_polySpace`: `polySpace` is stable under every `R(X)` (principal series:
  Library `rightDerivative_mem_principalSeries`). So `lie` acts on it, and
  `envelopingAction_inclusion_coe` identifies that action with the action on smooth functions.
* `iterate_rightDerivative_apply_one`: let `Q` be the Lagrange interpolation of the values
  `f(e(i))`, so `deg Q < k` (`Lagrange.degree_interpolate_lt`). By induction on `j`,
  `(R(E)^j f)(e(t)) = Q^{(j)}(t)` for all real `t`. The case `j = 0` is `IsRootPoly` at `g = 1`. For
  `j + 1`, both sides are derivatives of the two equal functions of step `j`
  (`hasDerivAt_rootUnit` and `Polynomial.hasDerivAt` composed with `ℝ → ℂ`), and derivatives are
  unique. At `j = k` and `t = 0`: `Q^{(k)} = 0` (`Polynomial.iterate_derivative_eq_zero`, or
  `Q = 0`), and `e(0) = 1`.
* `exists_eigen`: for upper `c`, `E_c` is upper triangular. On the principal series, `f(1) = 0`
  implies `(R(E_c) f)(1) = 0` (Library `RealPrincipalSeriesInfChar.rightDerivative_apply_one_eq_zero`).
  By `ComplexPrincipalSeriesInfChar.exists_eq_smul_of_ker_le`, `f ↦ (R(E_c) f)(1)` is a multiple
  `μ_c` of `f ↦ f(1)`. Choose `μ_c = 0` for the other positions.
* `eval_one_eq_zero_of_mem_J`: induction over the span. Put `F = z f`, which lies in
  `polySpace`. For a generator `(gen c - μ_c) z` with upper `c`, the value is
  `(R(E_c) F)(1) - μ_c F(1) = 0`. For `gen c₀ ^ k z`, it is `(R(E)^k F)(1) = 0`.
* `finrank_map_le_of_ker`: rank–nullity for `T` and `Ψ` restricted to `P`, together with
  `ker Ψ|_P ⊆ ker T|_P`.
* `finrank_map_le_of_isRootPoly`: let `χ = realPositionCharacter ds` and take `μ` from
  `exists_eigen`. Suppose `u ∈ U_d` and `[adU (nbar v) u] = 0` in `U / J` for all `v`. Let `h ∈ Y`
  and `F = u h`, a function of the principal series (Library
  `realStandardModule_le_principalSeries`). It is also `u` applied to `h` as a smooth function
  (`realStandardLie_coe`). By `rightTranslate_envelopingAction`,
  `F(nbar v) = ((adU (nbar v) u) · ρ(nbar v) h)(1)`. Here `ρ(nbar v) h ∈ polySpace` (Library
  `rightTranslation_mem_principalSeries` and `isRootPoly_rightTranslation`), so this is `0` by
  `eval_one_eq_zero_of_mem_J`. Hence `F = 0` (`eq_zero_of_nbar`). So the operator map vanishes on
  the kernel of `adMap μ c₀ k` in `U_d`. `finrank_map_le_of_ker` and `finrank_map_adMap_le` give
  the bound `((1 + n) d + 1)^N · k (d + 1)^(N - 1)`, with `|lowList c₀| = N - 1`. Finally
  `(1 + n) d + 1 ≤ (n + 2)(d + 1)` and `N + (N - 1) = n (n - 1) - 1` (`card_lowIdx_mul_two`).
