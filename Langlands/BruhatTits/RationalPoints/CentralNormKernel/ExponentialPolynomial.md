# Independence of exponential sequences and exponential polynomials

Author: Worker 1045.

This internal helper module proves two elementary uniqueness statements for
sequences of the form `k ↦ ∑ i, ν i ^ k * Q i (k)` over a field `K`, indexed by
`k : ℕ`. They are used in the proof of
`Langlands.BruhatTits.RationalPoints.CentralNormKernelCompactnessStatement`, to
recover the semisimple part of a central point from its powers. Both
statements are standard facts. This file does not formalize a cited source: the
statements and proofs were written for this proof route, at the request of the
route's first executor (Worker 1532). Nothing here involves group schemes.
Namespace: `Langlands.BruhatTits.RationalPoints.CentralNormKernel`.

## Constant coefficients over any field

`eq_zero_of_sum_mul_pow_eq_zero`: let `ν : ι → K` be injective, with `ι` a
finite type, and let `c : ι → K`. If `∑ i, c i * ν i ^ k = 0` for every
`k : ℕ`, then `c i = 0` for every `i`. No assumption on the characteristic is
needed, and some `ν i` may be zero.

Proof: the maps `k ↦ ν i ^ k` are distinct monoid homomorphisms
`Multiplicative ℕ → K` (`powersHom`), and distinct monoid homomorphisms into a
field are linearly independent (Dedekind–Artin, Mathlib's
`linearIndependent_monoidHom`). The hypothesis says that the linear combination
with coefficients `c` vanishes.

## Polynomial coefficients in characteristic zero

`eq_zero_of_sum_pow_mul_eval_eq_zero`: let `K` have characteristic zero, let
`ν : ι → K` be injective with every `ν i ≠ 0`, and let `Q : ι → K[X]`. If
`∑ i, ν i ^ k * (Q i).eval (k : K) = 0` for every `k : ℕ`, then every `Q i` is
the zero polynomial.

Both hypotheses on `ν` are necessary. If `ν i = 0`, the term `ν i ^ k` vanishes
for every `k ≥ 1`, so `Q i` is not determined by the sequence. In positive
characteristic `p`, the polynomial `X ^ p - X` vanishes on all of the image of
`ℕ` in `K`.

The proof is by induction on a bound `N` for the size
`∑ i, (if Q i = 0 then 0 else natDegree (Q i) + 1)`. This is the statement
`eq_zero_of_sum_pow_mul_eval_eq_zero_of_le`; the main theorem is its case where
`N` equals the size of `Q`.

- If the size is `0`, every `Q i` is zero.
- Otherwise, suppose some `Q j ≠ 0`. Apply the difference operator
  `a ↦ (k ↦ a (k + 1) - ν j * a k)` to the vanishing sequence. The result is the
  sequence of the same shape with coefficients
  `Q' i = C (ν i) * taylor 1 (Q i) - C (ν j) * Q i`, where `taylor 1 (Q i)` is
  `Q i (X + 1)`. So it also vanishes for every `k`.
- No `Q' i` is larger than `Q i`. The term for `j` strictly decreases:
  `Q' j = C (ν j) * (Q j (X + 1) - Q j)` has smaller degree than `Q j`, since
  the two terms have the same leading coefficient. So the induction hypothesis
  applies and every `Q' i` is zero.
- For `i ≠ j` with `Q i ≠ 0`, comparing leading coefficients in
  `C (ν i) * taylor 1 (Q i) = C (ν j) * Q i` gives `ν i = ν j`, which
  contradicts injectivity. Hence `Q i = 0` for all `i ≠ j`.
- The hypothesis then reads `ν j ^ k * Q j (k) = 0`. Since `ν j ≠ 0`, `Q j`
  vanishes at every natural number. These are infinitely many points of `K` in
  characteristic zero, so `Q j = 0`. This contradicts `Q j ≠ 0`.

## Declarations

- `eq_zero_of_sum_mul_pow_eq_zero`
- `eq_zero_of_sum_pow_mul_eval_eq_zero_of_le`
- `eq_zero_of_sum_pow_mul_eval_eq_zero`
