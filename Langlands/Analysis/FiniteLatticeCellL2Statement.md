# An L2 test from polynomial-geometric lattice cell bounds

`Langlands.FiniteLatticeCellL2Statement` is an internal analytic interface for
integrating coefficient estimates over a finite natural-number lattice.
It concerns an arbitrary measurable space, measure and almost everywhere
strongly measurable real function. It has no group or Haar hypothesis.

For a finite coordinate type `I`, cells indexed by `n : I → ℕ` cover the
whole space. The cells need not be measurable, disjoint or nonempty. The
coefficient bound on each cell is

`‖f x‖ ≤ C (1 + ∑ i, n i)^d ∏ i, (a i)^(n i)`.

The volume bound is

`μ (cell n) ≤ ENNReal.ofReal (D ∏ i, (w i)^(n i))`.

The constants `C`, `D` and the coordinate weights `a i`, `w i` are
nonnegative real numbers, and `d` is a natural number. For every coordinate
the residual weight `(a i)^2 * w i` must be strictly below one. The conclusion
is `MemLp f 2 μ`. The hypotheses allow zero weights and an empty coordinate
type; in the empty case the tuple space has one element.

The intended derivation squares the coefficient bound, multiplies it by the
volume bound, and combines coordinate powers into the residual geometric
weights. The resulting summand is a constant times
`(1 + ∑ i, n i)^(2*d) ∏ i, ((a i)^2 * w i)^(n i)`.
The published `finiteNatLatticeENNRealSummability` gives its finite sum,
and `countableCellLpUpper` gives the conclusion.

The interface is derived from those two published analytic results. It
supplies no Cartan cover, cell-volume estimate or representation coefficient
bound. Its use in the general rational strict Jacquet criterion requires
separate proofs of those actual geometric and representation-theoretic inputs.
