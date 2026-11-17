# The actual adjacent filtration away from positive linked indices

This internal assembly proves the full nonlinked branch of the two-induction-block
filtration. For every pair `d,e` in strictly ascending real exponent order,
if `IsLinkedAt d e k` fails for every natural `k`, then the actual
`GL₄(ℝ)` compact-finite standard module has the required adjacent filtration.
There is no half-weight-gap threshold, crossing-genericity condition or
restriction on the original weights.

For nonzero original weights, absence of a linked index implies that the
Mœglin data of the two blocks are unlinked. Their lists of data each contain
one discrete datum. A proposed linkedness equation with the positive exponent
gap gives `IsLinkedAt` at index `m-1`, where `m` is its positive natural gap
increment. The equation with the negative exponent gap contradicts the
strict ascending order after taking real parts.

Apply the published theorem `realInducedSwap` to the pair in descending order.
It supplies an injective exact intertwiner from the exchanged source to the
original target. The published `RealInducedPairKTypeTransport` result makes
this map surjective because both orders have the same compact type
multiplicities. Expressing its exact intertwining as intertwining modulo zero,
push forward the one-source identity filtration. Its only source is the
exchanged original pair, which is allowed in the adjacent-filtration definition.

If either original weight is zero, the published left-zero or right-zero
filtration proves the conclusion directly. Those cases need no linking
restriction.

`RealInducedPairUnlinkedFiltrationStatement` is the universally quantified
nonlinked-branch proposition, proved by `realInducedPairUnlinkedFiltration`.
The helper `exists_bijective_intertwiner` retains the nonzero-weight and
unlinked-data hypotheses of the swap theorem. This module uses only proved
Library results and elementary arithmetic; no irreducibility or classification
premise is retained. The remaining linked cases of
`RealInducedInducedFiltrationStatement` are not proved here.
