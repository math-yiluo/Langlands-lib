# A dimension count for divisibility by a bivariate polynomial

Module `Langlands.AlgebraicGeometry.LangWeil.Stepanov.DivisibleKernel`. It imports only
Mathlib (`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`,
`Mathlib.LinearAlgebra.Dimension.Constructions`, `Mathlib.Algebra.Polynomial.BigOperators`,
`Mathlib.Algebra.Polynomial.RingDivision`).

Throughout, a bivariate polynomial `p : Polynomial (Polynomial R)` is read as `p(X, Y)` with
outer variable `Y`. "`p` lies in the box `(a, b)`" means
`p.natDegree ≤ b ∧ ∀ i, (p.coeff i).natDegree ≤ a`: the `Y`-degree is at most `b` and every
coefficient has `X`-degree at most `a`. The module states this conjunction explicitly in each
lemma and introduces no definition for it.

## Main result

`exists_ne_zero_forall_dvd`. Let `F` be a field and `fh : Polynomial (Polynomial F)` nonzero, of
`Y`-degree `n = fh.natDegree`, with `(fh.coeff i).natDegree ≤ m` for all `i`. Let `V` be a
finite-dimensional `F`-vector space (in the same universe as `F`), `ι` a finite type,
`φ : ι → V →ₗ[F] Polynomial (Polynomial F)` and `a b : ι → ℕ`, such that `φ l v` lies in the box
`(a l, b l)` for all `l` and `v`. If

`∑ l, (n * (a l + 1) + m * (b l + 1 - n)) < Module.finrank F V`

(truncated subtraction in `ℕ`), then there is `v : V` with `v ≠ 0` and `fh ∣ φ l v` for every
`l`.

The binders are exactly those of the `DivisibleKernel` proposition requested by Worker 5406 for
the Task 5406 assembly, in the same order, all explicit. A check outside this module confirmed
that `exists_ne_zero_forall_dvd` proves that proposition verbatim, using only the standard
axioms.

## Auxiliary declarations

- `box_mul`: if `p` lies in the box `(a₁, b₁)` and `q` in `(a₂, b₂)`, then `p * q` lies in
  `(a₁ + a₂, b₁ + b₂)`. Here `R` is any commutative ring, as in the next four lemmas.
- `box_sub`, `box_sum`: each box is closed under subtraction and under finite sums.
- `box_monomial`: `monomial i (monomial j c)` lies in the box `(j, i)`.
- `eq_zero_of_box`: if `p` lies in the box `(a, b)` and `(p.coeff i).coeff j = 0` for all
  `i ≤ b`, `j ≤ a`, then `p = 0`.
- `box_count_le`: for all naturals,
  `(b + 1) * (a + 1) ≤ n * (a + 1) + m * (b + 1 - n) + (b + 1 - n) * (a + 1 - m)`.
- `boxCoeff F B A : Polynomial (Polynomial F) →ₗ[F] (Fin B × Fin A → F)` sends `p` to
  `k ↦ (p.coeff k.1).coeff k.2`, its coefficient array on `[0, B) × [0, A)`. `boxCoeff_apply`
  is its defining equation.
- `boxEncode F B A : (Fin B × Fin A → F) →ₗ[F] Polynomial (Polynomial F)` sends `q` to
  `∑ k, monomial k.1 (monomial k.2 (q k))`. `boxEncode_apply` is its defining equation.
  `boxEncode_coeff` shows that the encoding recovers its array:
  `((boxEncode F B A q).coeff i).coeff j = q (i, j)` for `i : Fin B`, `j : Fin A`.
- `boxMulEncode F fh B A`: `boxEncode` followed by left multiplication by `fh`.
  `boxMulEncode_apply` is its defining equation.
- `box_mul_boxEncode`: if `fh.natDegree ≤ n` and every coefficient of `fh` has `X`-degree at
  most `m`, then `fh * boxEncode F (b + 1 - n) (a + 1 - m) q` lies in the box `(a, b)`.
- `kernelMap F fh m n V ι φ a b`: the `F`-linear map
  `V × (Π l, Fin (b l + 1 - n) × Fin (a l + 1 - m) → F) → Π l, Fin (b l + 1) × Fin (a l + 1) → F`
  that sends `(v, q)` to
  `l ↦ boxCoeff F (b l + 1) (a l + 1) (φ l v - fh * boxEncode F (b l + 1 - n) (a l + 1 - m) (q l))`.
  `kernelMap_apply` states this formula.

## Provenance

This is the linear-algebra step of the Stepanov–Schmidt method (W. M. Schmidt, *Zur Methode
von Stepanov*, Acta Arithmetica 24 (1973)). It shows that an auxiliary polynomial can be
chosen divisible by the curve equation once the parameter space is large enough. The exact
formulation, with the bound `n (a + 1) + m (b + 1 - n)` on the codimension of the multiples of
`fh` inside the box `(a, b)`, is internal to the project. Worker 5406 specified it for the
plane-curve Hasse–Weil assembly (Task 5406). The other declarations are elementary
helpers.

## Proof

- **Counting.** Write `A = a + 1` and `B = b + 1`. If `B ≤ n`, the right-hand side of
  `box_count_le` is at least `n A ≥ B A`. If `B > n` and `A ≤ m`, write `B = n + k`; then
  `B A = n A + k A ≤ n A + m k`. Otherwise write `B = n + k` and `A = m + j`; then both sides
  equal `n A + m k + k j`.
- **Dimension comparison.** By `Module.finrank_prod`, `Module.finrank_pi_fintype` and
  `Module.finrank_fintype_fun_eq_card`, the target of `kernelMap` has dimension
  `∑ l, (b l + 1)(a l + 1)`. The source has dimension
  `finrank V + ∑ l, (b l + 1 - n)(a l + 1 - m)`. Summing `box_count_le` and using the
  hypothesis shows that the target dimension is strictly smaller.
- **Kernel element.** `LinearMap.ker_ne_bot_of_finrank_lt` and
  `Submodule.exists_mem_ne_zero_of_ne_bot` give `(v, q) ≠ 0` in the kernel.
- **Divisibility.** Fix `l`. The difference `φ l v - fh * boxEncode (q l)` lies in the box
  `(a l, b l)`: the first term by hypothesis, the second by `box_mul_boxEncode` (`box_sub`
  combines them). Its coefficient array on `[0, b l] × [0, a l]` vanishes, so it is `0` by
  `eq_zero_of_box`. Hence `φ l v = fh * boxEncode (q l)`, and `fh ∣ φ l v`.
- **Nonvanishing.** If `v = 0`, then `fh * boxEncode (q l) = 0` for each `l`. Since `fh ≠ 0`
  and `F[X][Y]` is a domain, `boxEncode (q l) = 0`, and `boxEncode_coeff` gives `q l = 0`. So
  `(v, q) = 0`, a contradiction.
