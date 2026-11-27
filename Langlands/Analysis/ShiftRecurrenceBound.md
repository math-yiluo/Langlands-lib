# Polynomial bounds for linear recurrences with roots in the closed unit disc

Module `Langlands.Analysis.ShiftRecurrenceBound`, namespace `Langlands.Analysis`. It depends only
on Mathlib.

## Contents

- `seqShift`: the shift `u ↦ (q ↦ u (q + 1))` on complex sequences, as a `ℂ`-linear
  endomorphism; `seqShift_apply`, `seqShift_pow_apply` and `aeval_seqShift_apply` (evaluating a
  polynomial `D` at the shift gives `q ↦ ∑_k D_k u(q + k)`).
- `norm_le_add_sum_of_recurrence`: if `u (q + 1) = c u q + v q` with `‖c‖ ≤ 1`, then
  `‖u q‖ ≤ ‖u 0‖ + ∑_{p < q} ‖v p‖`.
- `norm_le_of_aeval_seqShift_eq_zero`: if `∏_{c ∈ w} (S - c)` annihilates `u`, where `S` is the
  shift and every root satisfies `‖c‖ ≤ 1`, and `M ≥ 0` with `‖u j‖ ≤ M` for `j < |w|`, then
  `‖u q‖ ≤ 3^{|w|} (q + 1)^{|w|} M` for every `q`. The bound does not depend on the roots. The
  hypothesis `M ≥ 0` is needed for the empty list of roots (order zero), where `u = 0`.
- `aeval_seqShift_scaled`: for `κ ≠ 0`, rescaling a sequence by `κ^{-q}` divides the roots of an
  annihilating product by `κ`.
- `norm_le_of_translationSolution`: let `a` be an element of a monoid and `φ` a complex function
  with `∑_k c_k φ(a^k g) = 0` for all `g`, where `∏_{k<m} (X - w_k) = ∑_k c_k X^k` and
  `‖w_k‖ ≤ κ` (`κ > 0`). If `M ≥ 0` and `‖φ(a^j g)‖ ≤ κ^j M` for `j < m`, then
  `‖φ(a^q g)‖ ≤ 3^m (q + 1)^m κ^q M` for every `q`, including the case `m = 0`.

## Proofs

`norm_le_of_aeval_seqShift_eq_zero` is proved by induction on the list of roots. For
`w = c :: w'`, the sequence `v p = u (p + 1) - c u p` is annihilated by the product over `w'`.
Its first `|w'|` terms are bounded by `2M`, so by induction `‖v p‖ ≤ 3^{|w'|} (p + 1)^{|w'|} 2M`.
`norm_le_add_sum_of_recurrence` then bounds `‖u q‖` by `M + q · 3^{|w'|} (q + 1)^{|w'|} 2M`,
which is at most `3^{|w|} (q + 1)^{|w|} M`.

`norm_le_of_translationSolution` applies this to `v q = φ(a^q g) / κ^q`. By
`aeval_seqShift_scaled`, `v` is annihilated by the product with roots `w_k / κ`, which lie in the
closed unit disc.

## Source

This is an elementary estimate in the role of the polynomial factor `(1 + ‖log m_P(g)‖)^{deg}` in
Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), Lemma I.4.1, printed
p.49, and of the Lemma of I.4.2, printed p.51 (registered as
`moeglin-waldspurger-1995-spectral-decomposition`). There the factor comes from the finite
expansion of an automorphic form in exponential polynomials along `A_P`. Here the expansion is
replaced by a difference equation along one translation, so coinciding exponents need no
separate treatment.
