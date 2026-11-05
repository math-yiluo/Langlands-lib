# Valuation-theoretic Hensel lemmas for unit norm surjectivity

Author: Worker 1512. This is the first helper module of the proof of
`Langlands.ClassFieldTheory.Local.SeparableInertiaUnitNormSurjectivity` (see
`SeparableInertiaNormProof.md`). It imports only Mathlib.

All declarations are in the namespace
`Langlands.ClassFieldTheory.Local.SeparableInertiaNorm`. Throughout, `K` is a
field and `v : Valuation K ℝ≥0` is a real valuation. The *integers* of `v` are
the elements `x` with `v x ≤ 1`, and the *maximal ideal* consists of those with
`v x < 1`. No completeness, discreteness or characteristic assumption is made.

## Hypothesis predicates

These four `Prop`-valued definitions are internal interfaces for the later
modules. They are not literature statements.

- `ValHensel v`: simple-root Hensel lifting. For every monic `f : K[X]` with
  integral coefficients and every integral `a₀` with `v (f.eval a₀) < 1` and
  `v (f.derivative.eval a₀) = 1`, there is a root `a` of `f` with
  `v (a - a₀) < 1`. This is the usual Henselian property of the valuation ring
  `{x | v x ≤ 1}`, written in terms of `v`.
- `ValResidueRoot v`: every polynomial with integral coefficients, one of which
  in positive degree has value `1`, has an integral `b` with
  `v (f.eval b) < 1`. This is how "the residue field is algebraically closed"
  is used: the reduction of `f` modulo the maximal ideal is nonconstant, so it
  has a root.
- `ValUniformizer v π`: `0 < v π < 1`, and every nonzero integral `b` has
  `v b = v π ^ k` for some natural number `k`.
- `IntPoly v f`: every coefficient of `f` is integral.

`SeparableInertiaNormAmbient` derives the first three from the standard
ring-theoretic notions: a Henselian valuation ring, an algebraically closed
residue field, and a discrete valuation ring.

## Elementary lemmas

- `IntPoly.add`, `IntPoly.sum`, `IntPoly.C_mul_X_pow`, `IntPoly.X_pow`: closure
  of integral polynomials under sums and monomials with integral coefficients.
- `val_eval_le_one`: an integral polynomial takes integral values at integral
  points (ultrametric inequality on `eval_eq_sum_range`).
- `val_sum_mul_pow_le_one`: the same bound for a finite sum `∑ c k * a ^ e k`.
- `val_neg_one : v (-1) = 1` and `val_natCast_le_one : v (m : K) ≤ 1`, by
  induction on `m`.

## Strong Hensel lemma

`exists_root_one_add_of_hensel` states the following. Assume `ValHensel v`,
`v a0 < 1`, and that `c k` is integral for every `k`. Then there is `y` with
`v y < 1` and

`a0 + y + ∑_{2 ≤ k < n} c k * y ^ k = 0`.

The linear coefficient is a unit but the polynomial is not monic, so
`ValHensel` does not apply directly. The proof reverses the polynomial.

1. If `a0 = 0`, take `y = 0`.
2. Otherwise let `N = n + 2` and let `R` be the private polynomial
   `revPoly N n a0 c = X ^ N + X ^ (N - 1) + ∑_{2 ≤ k < n} C (a0 * c k * a0 ^ (k - 2)) * X ^ (N - k)`.
   It is monic (`revPoly_monic`, by a degree bound) and integral
   (`revPoly_intPoly`).
3. At `W = -1`, the leading terms cancel, so `R.eval (-1) = a0 * s` with `s`
   integral (`revPoly_eval`). Hence `v (R.eval (-1)) < 1`. The derivative is
   `(-1) ^ (n + 1) + a0 * s'` with `s'` integral (`revPoly_derivative_eval`),
   so it has value `1`.
4. `ValHensel` gives a root `W` of `R` with `v (W + 1) < 1`. Then `v W = 1`,
   so `W ≠ 0`.
5. Put `y = a0 / W`, so `v y = v a0 < 1`. A direct computation (`field_simp`)
   shows `W ^ N * (a0 + y + ∑ c k * y ^ k) = a0 * R.eval W = 0`. Since
   `W ^ N ≠ 0`, this gives the required equation.

The module is used by the cyclic step (`SeparableInertiaNormCyclic`), where
the strong Hensel lemma makes the group of unit norms open.
