# Evaluation of convergent bilateral series

This internal analytic helper uses the existing unrestricted bilateral coefficient
module and its actual finite Laurent action. `AbsolutelySummableAt x a` means
summability of the real norms of the complex terms `a m * x ^ m`, over every integer
`m`. The following results use an actual nonzero complex unit `x`.

The shift lemma reindexes the sum by the bijection `m ↦ m - k`. The integer-power
identity at a nonzero point then gives the factor `x ^ k`. The Laurent-action
lemma inducts over finite sums of Laurent monomials: a monomial acts by precisely
this coefficient shift and scalar multiplication, and addition preserves sums.
It follows that finite Laurent multiplication preserves absolute convergence,
using the equivalence of summability and norm summability in finite-dimensional
complex space.

The coefficients embedded from a finite Laurent polynomial have a bilateral sum
equal to `laurentEval x P`. This is proved by the same Laurent-monomial induction:
the coefficients of `C c * T k` vanish outside the singleton `{k}`, so the sum is
`c * x ^ k`. In particular, the embedded polynomial satisfies
`AbsolutelySummableAt (x : ℂ)` at every unit `x`. Finally,
`tsum_laurent_smul` applies the Laurent-action sum theorem to the sum supplied by
absolute convergence. It identifies the actual `tsum` of the finite convolution
with `laurentEval x P` times the original `tsum`.

These are internal consequences of the published bilateral action, Laurent
evaluation and standard convergence APIs. They are supporting lemmas for the
adjacent-rank analytic construction, with no new source theorem claimed.

The input coefficients have no support bound. These lemmas do not cancel a
Laurent polynomial on the bilateral module. They do not prove spectral coefficient
uniqueness or connect rational continuation values with formal coefficient
identities; those later steps require separate hypotheses and proofs.
