# Alternating refinement cancellation

This internal finite-sum construction implements the cancellation in the proof
of Aubert's Theorem 1.7(3), printed p.2183 (1995). It acts on an arbitrary
function from ordered positive block shapes to an additive commutative group,
using its canonical integer action, and makes no
claim about representation functors by itself.

`refinementAlternatingSum` sums over a coarse shape `B` and a refinement `S`,
with coefficient `(-1)^(n-B.length) * (-1)^(n-(B.flatten S).length)`.
`refinementCutsEquiv` replaces `S` by its flattened shape `C` with
`B.cuts ⊆ C.cuts`. Exchanging the finite sums gives
`refinementSquareCoefficient C` times the value at `C`.

The sign of any shape `B` is `(-1)^(n-1) * (-1)^B.cuts.card`: its cuts and
uncuts partition the `n-1` interior edges. Thus the sum over possible coarse
shapes is an alternating powerset sum. Mathlib's powerset cancellation
shows that its coefficient is zero unless `C.cuts` is empty. In that case
the two remaining signs have product one. The result is exactly the value at
the shape with no cuts.

All finite ordinal and complement calculations include `n = 0`, where there
are no interior edges. No positive-rank assumption is used.
