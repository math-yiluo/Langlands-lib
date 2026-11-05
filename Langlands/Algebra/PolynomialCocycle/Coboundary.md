# Symmetric polynomial 2-cocycles are coboundaries

Module: `Langlands.Algebra.PolynomialCocycle.Coboundary`.

This module proves the polynomial cocycle lemma `exists_coboundary`. It is internal to
the proof of `Langlands.GroupScheme.RelativeRoot.SplitUnipotentStableVectorSubgroupStatement`.
There it shows that an extension of `G_a` by a vector group, commutative and of exponent
`p`, splits as a group. The cocycle is that of a scheme-theoretic section of the
extension. The lemma and its proof were derived for this proof. Its characteristic-zero
case, and the characteristic-`p` case without the torsion condition, belong to the
classical theory of symmetric 2-cocycles (Lazard's lemma); see
`Langlands.Algebra.PolynomialCocycle.Homogeneous`.

A bivariate polynomial is an iterated polynomial `c : R[X][X]` (Mathlib's
`Polynomial.Bivariate`). The inner variable is the first argument: for elements `x`,
`y` of an `R`-algebra, `aevalAeval x y c` is `∑_j (c.coeff j)(x) · y^j`. So the
coefficient of `x^i y^j` is `(c.coeff j).coeff i`.

## Declarations

Evaluation lemmas, for a commutative ring `R`:

- `coeff_taylor_X_map_C p n`: for `p : R[X]`, the `n`-th coefficient of the Taylor
  expansion `taylor X (p.map C)` in `R[X][X]` is the Hasse derivative `hasseDeriv n p`.
- `aeval_X_add_C_X p`: `aeval (X + C X) p = taylor X (p.map C)` in `R[X][X]`.
- `coeff_coeff_swap c i j`: `((swap c).coeff j).coeff i = (c.coeff i).coeff j`, where
  `swap` exchanges the two variables.
- `aevalAeval_eq f`: an `R`-algebra map `f : R[X][X] →ₐ[R] A`, with `A` a commutative
  semiring, equals `aevalAeval (f (C X)) (f X)`.
- `aevalAeval_C_X_X`: `aevalAeval (C X) X` is the identity of `R[X][X]`.
- `aevalAeval_term₁`, …, `aevalAeval_term₄`: the four evaluations of `c` at the universal
  triple `(u, v, w) = (C (C X), C X, X)` in `R[X][X][X]` that appear in the cocycle
  identity:
  - `c(u, v) = C c`;
  - `c(u + v, w) = c.map (aeval (X + C X))`;
  - `c(v, w) = c.map (aeval X)`;
  - `c(u, v + w) = taylor X (c.map C)`.
- `coeff_coeff_coeff_C`, `coeff_coeff_coeff_term₂`, `coeff_coeff_coeff_term₃`,
  `coeff_coeff_coeff_term₄`: their coefficients of `u^a v^b w^e`. They are
  `[e = 0] C'(a, b)`, `C(a + b, b) · C'(a + b, e)`, `[a = 0] C'(b, e)` and
  `C(b + e, e) · C'(a, b + e)`, where `C'(i, j) = (c.coeff j).coeff i`.
- `coeff_aevalAeval_C_mul_X_X c r n`: the `n`-th coefficient of `c(r X, X)` in `R[X]` is
  `∑_{l ≤ n} C'(l, n - l) · r^l`.

The rest of the module works over a field `k : Type u`. The hypotheses quantify over all
commutative `k`-algebras `R : Type u`.

- `coeff_rel c hcoc a b e`: if `c(x, y) + c(x + y, z) = c(y, z) + c(x, y + z)` in every
  such `R`, then
  `[e = 0] C'(a, b) + C(a + b, b) · C'(a + b, e) = [a = 0] C'(b, e) + C(b + e, e) · C'(a, b + e)`.
- `coeff_symm c hsymm i j`: if `c(x, y) = c(y, x)` in every such `R`, then
  `C'(i, j) = C'(j, i)`.
- `coeff_tors c m htors n`: if `∑_{i < m} c(i x, x) = 0` in every such `R`, then
  `∑_{l ≤ n} powerSum k m l · C'(l, n - l) = 0`.
- `coeff_zero_of_pos c hrel he`: under the coefficient form of the cocycle identity (the
  conclusion of `coeff_rel`), `C'(0, e) = 0` for `e > 0`.
- `isHomCocycle_of_coeff c hsymm hrel hn`: under the coefficient forms of symmetry and of
  the cocycle identity, for `n > 0` the degree-`n` part `l ↦ C'(l, n - l)` satisfies
  `IsHomCocycle n`.
- `exists_coeff_eq_choose c hsymm hrel htors`: under the coefficient forms of symmetry, of
  the cocycle identity, and of the torsion condition with `m = ringChar k`, there is
  `g : ℕ → k` with `C'(i, n - i) = g n · C(n, i)` for all `0 < i < n`.
- `aeval_C_X G`: `aeval (C X) G = C G` in `k[X][X]`.
- `exists_coboundary c hsymm hcoc htors`: suppose `c : k[X][X]` satisfies, in every
  commutative `k`-algebra `R : Type u`:
  - symmetry, `c(x, y) = c(y, x)`;
  - the cocycle identity, `c(x, y) + c(x + y, z) = c(y, z) + c(x, y + z)`;
  - the torsion condition, `∑_{i < ringChar k} c(i x, x) = 0`.

  Then there is `G : k[X]` with `c(x, y) = G(x + y) - G(x) - G(y)` in every commutative
  `k`-algebra `R : Type u`. In characteristic zero `ringChar k = 0`, so the torsion
  condition is the empty sum and holds automatically. No normalization of `c` is
  assumed: the constant term of `c` is matched by the constant term of `G`.

## Proof

The coefficient lemmas specialize the hypotheses to universal points:

- `coeff_rel` uses the cocycle identity at `(C (C X), C X, X)` in `k[X][X][X]` and compares
  coefficients with the four `coeff_coeff_coeff` lemmas. These come from `hasseDeriv_coeff`.
- `coeff_symm` uses symmetry at `(C X, X)` in `k[X][X]`, which says `c = swap c`.
- `coeff_tors` uses the torsion condition at `x = X` in `k[X]`, then
  `coeff_aevalAeval_C_mul_X_X` and an exchange of sums.
- `coeff_zero_of_pos` is the case `a = b = 0`, `e > 0` of the coefficient relation.
- For `isHomCocycle_of_coeff`: `zero` is `coeff_zero_of_pos`; `top` is `coeff_zero_of_pos`
  after symmetry; `symm` is symmetry; `coc` is the coefficient relation with
  `a, b > 0` and `e = n - a - b > 0`.

`exists_coeff_eq_choose` treats each `n > 0` separately and then chooses the
coefficients. By `CharP.char_is_prime_or_zero`, `ringChar k` is a prime `p` or `0`. In
the first case apply `IsHomCocycle.exists_eq_charP` with `p = ringChar k`. In the second,
`k` has characteristic zero; apply `IsHomCocycle.exists_eq_charZero`.

For `exists_coboundary`, let `g` be as above and `N = c.natDegree`. By symmetry,
`C'(i, j) = 0` whenever `i + j > 2N`. Let `G` be the polynomial of degree `≤ 2N` with
`G_0 = -C'(0, 0)` and `G_n = g n` for `0 < n ≤ 2N`. In `k[X][X]`,
`aeval (C X + X) G = taylor X (G.map C)`, `aeval (C X) G = C G` and
`aeval X G = G.map C`. So the coefficient of `x^i y^j` in `G(x + y) - G(x) - G(y)` is
`C(i + j, j) · G_{i+j} - [j = 0] G_i - [i = 0] G_j`. Compare with `C'(i, j)` in four
cases:

- `i = j = 0`: both sides are `C'(0, 0)`.
- Exactly one of `i`, `j` is zero: both sides vanish, by `coeff_zero_of_pos` (and
  symmetry when `j = 0`).
- `i, j > 0`: if `i + j ≤ 2N`, the claim is `C'(i, j) = C(i + j, i) · g (i + j)`, which is
  `exists_coeff_eq_choose`. Otherwise both sides vanish.

This proves `c = G(C X + X) - G(C X) - G(X)` in `k[X][X]`. Applying the algebra map
`aevalAeval x y` and `aeval_algHom_apply` gives the identity at any `x, y` in any `R`.
