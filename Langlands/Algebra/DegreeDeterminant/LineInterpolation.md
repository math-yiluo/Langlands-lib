# Functions on `ℕ ^ n` that are polynomial along coordinate lines

This module proves a lemma about multivariate polynomials. It defines nothing new.

## Main result

`Langlands.Algebra.DegreeDeterminant.exists_mvPolynomial_of_line`: let `K` be a field of characteristic zero, `D` a natural number and `f : (Fin n → ℕ) → K`. Suppose that for every coordinate `i` and every point `x` there is a polynomial `R : K[X]` with `R.natDegree ≤ D` and `f (Function.update x i (x i + m)) = R.eval m` for all natural numbers `m`. Then there is `M : MvPolynomial (Fin n) K` with `f x = MvPolynomial.eval (fun i => (x i : K)) M` for every `x : Fin n → ℕ`.

## Proof

The proof is by induction on `n`.

- `eval_eq_sum_lagrange`: a polynomial `R` of degree at most `D` satisfies `R(t) = ∑_{k ≤ D} R(k) · L_k(t)`, where `L_k` is the Lagrange basis polynomial at the nodes `0, …, D` (Mathlib's `Lagrange.basis`, nodes cast to `K`). This is Mathlib's `Lagrange.eq_interpolate`.
- `eval_aeval_X`: evaluating the one-variable polynomial `p` in the variable `X i` at `v` gives `p.eval (v i)`.
- For `n = 0` the function is constant. For `n + 1`, write `x = Fin.cons m x'`. For each `k`, the function `x' ↦ f (Fin.cons k x')` is again polynomial along coordinate lines (by `Fin.cons_update`), so the induction hypothesis gives `M k`. Along the first coordinate, `m ↦ f (Fin.cons m x')` is a polynomial of degree at most `D`, so `f (Fin.cons m x') = ∑_{k ≤ D} f (Fin.cons k x') · L_k(m)`. The polynomial `∑_{k ≤ D} L_k(X 0) · rename Fin.succ (M k)` therefore represents `f`.

## Provenance

This is the elementary fact behind the first sentence of the proof of Proposition 12.4 in Milne, *Abelian Varieties* (author revision 2022, p. 21): a function that is polynomial along lines is a polynomial function. The Lagrange-interpolation proof is standard; it is used here only for natural-number points.
