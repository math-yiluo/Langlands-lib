# A Taylor condition on `O(n)` making principal-series functions polynomial along a root group

Lean module: `Langlands.Representation.Archimedean.RealTaylorLeftPolynomial`
(namespace `Langlands.Archimedean`).

This module defines one statement, `RealTaylorLeftPolynomialStatement`. The statement is not
proved here. It uses `lowerRootMatrix n p hp` (the matrix unit `E = E_{p+1,p}`) and
`lowerRootElement n p hp t` (the element `e(t) = 1 + t E` of `GL_n(ℝ)`) from module
`RealLeftPolynomialGrowth`.

## The statement

```lean
def RealTaylorLeftPolynomialStatement : Prop :=
  ∀ (n : ℕ) (χ : ℕ → ℝˣ → ℂ) (p k : ℕ) (hp : p + 1 < n),
    (∀ x : ℝˣ, 0 < (x : ℝ) → χ (p + 1) x = ((x : ℝ) : ℂ) ^ k * χ p x) →
    ∀ h ∈ principalSeries ℝ n χ,
      (∀ κ ∈ unitaryCompact ℝ n,
        (rightDerivative (matrixModel ℝ n) (lowerRootMatrix n p hp))^[k]
          (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) κ h) 1 = 0) →
      ∀ g : Langlands.GeneralLinear n ℝ, ∃ q : Polynomial ℂ, q.degree < k ∧
        ∀ t : ℝ, h (lowerRootElement n p hp t * g) = q.eval (t : ℂ)
```

The data are:

- functions `χ : ℕ → ℝˣ → ℂ`, the position characters of the smooth principal series
  `principalSeries ℝ n χ` of `GL_n(ℝ)`. That space consists of the smooth `h` with
  `h(diag(a) u g) = Π_i χ_i(a_i) |a_i|^((n-1)/2 - i) h(g)` for `u` upper unitriangular;
- a position `p` with `p + 1 < n` and `k : ℕ`.

The hypotheses are:

1. **Exponent condition**: `χ_{p+1}(x) = x^k χ_p(x)` for every `x > 0`. Nothing is assumed for
   `x < 0`.
2. **Taylor condition on `O(n)`**: for every `κ ∈ O(n)` (`unitaryCompact ℝ n`), the `k`-fold
   iterated right derivative along `E` of the right translate `g ↦ h(g κ)` vanishes at the
   identity. `rightDerivative (matrixModel ℝ n) E f g` is the derivative of `x ↦ f(g x)` at
   `x = 1` in the direction `E`. For smooth `f` this is `d/dt f(g e(t))` at `t = 0`, since
   `t ↦ e(t)` is a one-parameter subgroup with tangent `E`. So the condition says
   `d^k/dt^k h(e(t) κ) = 0` at `t = 0`.

The conclusion: for every `g ∈ GL_n(ℝ)` there is a complex polynomial `q` of degree `< k` with
`h(e(t) g) = q(t)` for all real `t`.

For `k = 0` the Taylor condition says `h(κ) = 0` on `O(n)`, so `h = 0`, and `q = 0` works.

The `χ_i` are not assumed multiplicative. If `h ≠ 0`, the equivariance of `h` forces
`χ_i = c_i ψ_i` with characters `ψ_i` and constants `c_i` with `Π c_i = 1`. At `x = 1` the
exponent condition gives `c_{p+1} = c_p`, so it holds with `ψ` in place of `χ`. Hence the
statement reduces to the case of characters.

## Provenance

This is an internal statement, introduced in Task 7070. It is one of three statements whose
combination, proved in module `RealLinkedJacquetFunctional`
(`realLinkedQuotientGrowth_of_split`), gives `RealLinkedQuotientGrowthStatement`.

For `GL_2(ℝ)` and `p = 0` it is a classical fact. Restrict `h` to the lower unipotent group
`t ↦ e(t)`. The exponent condition makes `G` act there by `f ↦ (c t + d)^(k - 1) f(γ t)` near
`t = 0`. Bol's identity says that `d^k/dt^k` intertwines this action with weight `1 - k` and the
one with weight `1 + k`. So `d^k/dt^k` maps the principal series into another principal series.
The statement is the `GL_n` form of this: a function whose image vanishes on `O(n)` is
polynomial along `e(t)`. No single published reference states it in this form.

## Suggested proof route

This route is not part of this module and is recorded only as guidance.

1. Put `H(g) = d^k/dt^k h(e(t) g)` at `t = 0`. Then `d^k/dt^k h(e(t) g)` at `t = s` is
   `H(e(s) g)`. So it suffices to show `H = 0`: then `t ↦ h(e(t) g)` has vanishing `k`-th
   derivative on `ℝ` and is a polynomial of degree `< k`.
2. `H` is left equivariant under the upper triangular Borel subgroup `B` for some character:
   - For the diagonal torus, `e(t) a = a e(t a_p / a_{p+1})`. So `H(a g)` is
     `(a_p / a_{p+1})^k` times the principal-series factor of `a` times `H(g)`.
   - The upper unitriangular matrices with entry `(p, p + 1)` equal to `0` form a group `N'`.
     `e(t)` normalises `N'`, and `h` is left `N'`-invariant, so `H(u g) = H(g)` for `u ∈ N'`.
   - For the root group `x(s) = 1 + s E_{p,p+1}`, write `e(t) x(s)` as an upper triangular
     element times `e(t / (1 + t s))`, for `1 + t s ≠ 0`. With the exponent condition, the
     upper triangular factor contributes `(1 + t s)^(k - 1)` near `t = 0`. Bol's identity then
     gives `H(x(s) g) = H(g)`. Only `t` near `0` matters, so only `x > 0` in the exponent
     condition is used.
3. The hypothesis says `H = 0` on `O(n)`. `GL_n(ℝ) = B · O(n)` (Iwasawa), so `H = 0`. The Library
   lemma `eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact` (module
   `RealStandardModuleAdmissible`) needs `H` in a principal series. Smoothness of `H` follows
   from that of `h`, and its equivariance from step 2.
