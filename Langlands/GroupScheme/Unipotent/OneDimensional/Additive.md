# Additive polynomials and the Euclidean algorithm for them

Worker 716. Internal lemmas for the proof of
`Langlands.GroupScheme.PerfectFieldOneDimensionalUnipotentStatement`. The
facts are standard (additive polynomials over a field of characteristic `p`
are `p`-polynomials, and over a perfect field they admit a Euclidean division
algorithm). No registered source was used; the proofs below are the ones
implemented in Lean.

## Definitions

`IsAdditive f`, for `f : k[X]`, means `coboundary f = 0`, i.e.
`f(X + Y) = f(X) + f(Y)` in `k[X][Y]` (see `Cocycle`). By `IsAdditive.aeval_add`,
an additive polynomial satisfies `f(u + v) = f(u) + f(v)` in every commutative
`k`-algebra.

## Closure properties

`isAdditive_zero`, `isAdditive_X`, `IsAdditive.add`, `.neg`, `.sub`, `.C_mul`
and `.comp` state that additive polynomials form a subspace closed under
composition containing `X`. For the characteristic exponent `q`,
`isAdditive_X_pow` shows that `X^{q^n}` is additive (Mathlib
`add_pow_expChar_pow`). `IsAdditive.coeff_zero` and `IsAdditive.aeval_zero`
show that an additive polynomial has no constant term.

## Degrees

`IsAdditive.choose_eq_zero` compares the coefficient of `X^{n-j} Y^j` in
`coboundary f = 0`, where `n = natDegree f` and `0 < j < n`. It shows that the
binomial coefficient `choose n j` vanishes in `k`.

`eq_pow_of_dvd_choose` is an elementary number-theoretic lemma, proved by strong
induction. If a prime `p` divides every `choose n j` with `0 < j < n`, then `n`
is a power of `p`. If `p ∣ n = p m`, then Lucas's theorem
(`Choose.choose_modEq_choose_mod_mul_choose_div_nat`) gives
`choose (p m) (p j) ≡ choose m j`, and the induction hypothesis applies to `m`.
Otherwise `p ∤ choose n 1 = n`, which forces `n = 1`.

`IsAdditive.natDegree_eq_pow` follows: a nonzero additive polynomial has degree
`q^a` for the characteristic exponent `q`. In characteristic zero, `choose n 1 = n`
must vanish unless `n = 1`.

## Reduction and Euclid

`exists_reduce` performs leading-term elimination. Assume `k` is perfect and
`α, β` are nonzero additive polynomials with `deg β ≤ deg α`. Write
`deg α = q^a` and `deg β = q^b`. Then `ρ = e X^{q^{a-b}}` is additive, where
`e` is the `q^b`-th root (via `iterateFrobeniusEquiv`) of the quotient of the
leading coefficients. Either `α - β ∘ ρ = 0` or it has smaller degree than `α`.

`exists_common_of_relation` is Euclid's algorithm. Let `P` be a subset of a
`k`-algebra `B` with the following properties:

- `P` is closed under additive polynomials and under subtraction;
- if `u ∈ P` and a nonzero polynomial vanishes at `u`, then `u = 0`.

If `u, v ∈ P` satisfy `α(u) = β(v)` for nonzero additive `α, β`, then there are
`s ∈ P` and additive `A, A'` with `u = A(s)` and `v = A'(s)`.

The proof is strong induction on `deg α + deg β`. By symmetry, assume
`deg β ≤ deg α` and take `ρ` from `exists_reduce`. The relation becomes
`(α - β ∘ ρ)(u) = β(v - ρ(u))`, using additivity of `β`.

- If `α = β ∘ ρ`, then `β(v - ρ(u)) = 0` forces `v = ρ(u)`. Take `s = u`.
- Otherwise the degree sum drops. The induction hypothesis applied to the pair
  `(u, v - ρ(u))` gives `s`, and `v = A''(s) + ρ(A(s))` is again an additive
  polynomial in `s`.
