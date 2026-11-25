# Cuspidal pair logarithmic series and their boundary limits

`Langlands.Global.CuspidalPairLogAsymptoticsAt.{u, uQ} F` is a fieldwise
proposition for pairs of actual cuspidal realizations with unitary central
characters, trivial on the split centre. Their presentations of universe `uQ`
have irreducible admissible finite local components. A single finite set `S`
contains the exceptional sets of both presentations.

For each real `θ`, divide the pair logarithmic series at `σ + iθ` by
`log(1/(σ−1))`. The proposition gives its limit as real `σ` decreases to 1.
The limit is 1 when `θ = 0` and the first realization is the contragredient
of the second, including equality of ranks. In all other cases the limit is
0. The series uses `logEulerTerm` from the published absolute convergence
module, with power `k = n + 1` for each `n : ℕ` and the product of the two
power traces. The comparison with a conjugated trace uses a presentation of
the contragredient on the first side.

This is the form of Jacquet–Shalika II, Theorem 4.1, printed pp. 805–806
(PDF pp. 30–31), used by the independence proof after normalization on the
split centre. The vertical shift accounts for the imaginary part of a
complex norm-power twist. The module supplies this property as a premise of
the independence proof.

`norm_logEulerTerm_le_of_le_re` bounds the absolute value of each term at
`s` by its absolute value at a real `σ ≤ Re s`, using the nonnegative
logarithmic exponent `k log qᵥ`. `tendsto_log_inv_sub_one` proves the
divergence of the normalizing denominator by composing the right-hand limit
of `σ − 1` with reciprocation and the real logarithm. These are internal
analytic lemmas for the summation in Theorem 4.2, printed p. 807 (PDF p. 32).
