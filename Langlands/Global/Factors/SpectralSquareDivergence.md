# Divergence of the series of squared power traces

`Langlands.Global.SpectralSquareDivergenceStatement` concerns spectra of a
fixed positive rank `n`, assigned to the finite places of a number field
`F` outside a finite set `S`. If each such spectrum has an eigenvalue of
norm at least one, the series with coefficient `|tr Aᵥᵏ|²/k` and
exponent `k log qᵥ` diverges at the positive real point
`1 / (n [F : ℚ])`. Here `k` ranges over positive integers and `qᵥ`
is the residue-field cardinality.

Enumerate a spectrum as an `n`-tuple. Its supremum norm is at least one,
so the uniform power-sum estimate gives one power `1 ≤ k ≤ n` whose trace
has norm at least a constant `ε > 0` depending only on `n`. Choose a
finite place over each rational prime `p`. The chosen places are distinct
by contraction of their prime ideals. The norm formula and the sum of
the ramification indices times the inertia degrees give
`qᵥ ≤ p^[F : ℚ]`. Discard the finitely many primes with chosen place in
`S`.

At `1 / (n [F : ℚ])`, the term chosen over `p` is at least `ε²/(np)`.
Summability would imply summability of the reciprocal primes outside a
finite set, contradicting `Nat.Primes.not_summable_one_div` in Mathlib.

This internal arithmetic estimate is used in the Landau argument for
cuspidal pair rigidity. The series can use one Satake spectrum or a
concatenation of two spectra with one multiplied by a unitary phase.
