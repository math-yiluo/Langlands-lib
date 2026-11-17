# Finite propagation of adjacent compact rotation modes

This internal algebraic result uses the mode-decomposition interface of
`RealOrthogonalUncertainty`. Let `a,b,c` be complex-linear operators with
`[a,b]=c` and `[c,a]=b`. Suppose the supplied projections `π_m` form the
finite mode decomposition of `a` with eigenvalues `i m`.

If all `a`-modes of `v` satisfy `|m|<n`, then those of `b v` satisfy
`|m|<n+1`, those of `b^d v` satisfy `|m|<n+d`, and those of `Q(b)v`
satisfy `|m|<n+Q.natDegree`.

The published raising and lowering identities express `b` as half the sum
of operators shifting the mode index by one in opposite directions.
This proves the one-step bound, and induction proves the power bound.
Expand polynomial evaluation into its coefficient-weighted powers and use
linearity of each projection to prove the polynomial bound. No
finite-dimensionality hypothesis on the whole vector space is needed.

`RealRotationFinitePropagationStatement` collects the polynomial bound for
every complex module, operator triple, finite mode decomposition, vector and
polynomial with exactly these two commutator hypotheses.
`realRotationFinitePropagation` proves it. The helper lemmas also work in
arbitrary universes.

These are algebraic mode bounds. This module does not identify any actual
tail multiplier with a polynomial, transport these bounds to ambient
standard modules, or prove a linked two-block kernel-image assertion.
