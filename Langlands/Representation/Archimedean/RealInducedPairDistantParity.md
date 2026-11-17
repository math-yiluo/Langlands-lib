# Distant linked filtration with a free internal parity

This internally derived result removes the canonical parity assumption from the sufficiently distant linked case. It concerns the actual `O(4)`-finite standard modules. The unconditional `RealInducedInducedFiltrationStatement` remains open.

For complex character data `d,e` and a natural number `k`, write `L=d.weight.natAbs`, `M=e.weight.natAbs`, `P=outerWeight d e k=max L M+k+1`, and `H=innerWeight d e k=k+1-min L M`, with `H` an integer. `RealInducedPairDistantParityFiltrationStatement` states that `L>0`, `M>0`, `IsLinkedAt d e k`, and `L²+M²<H.toNat²` imply the actual `RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)`. The theorem `realInducedPairDistantParityFiltration` proves this proposition. No hypothesis on the parity of `P-M` occurs.

## Choice of the quotient presentation

The actual quotient presentation permits arbitrary internal parities `sd,se : Fin 2`. Set `u=lo d sd`, `v=hi d sd`, `x=lo e se`, and `y=hi e se`. Changing these internal choices does not change the original complex character data or the induced-block target. Endpoint exponents and their differences are also unchanged. The temporary compatibility hypothesis for the construction is

`Even ((P : ℤ)-1-pairParity u y)`.

`differences` reuses the endpoint computation from `RealInducedPairDistantFiltration`: the differences for the four crossings are `P,H+L,H+M,H`. The identity `H+L+M=P` implies that the compatibility hypothesis also gives the reducible inner parity when `H>0`. It gives the same-parity integral generic parameters for both middle crossings. `inner_parity` proves the first assertion, and `exists_ascendingData` proves the latter assertions and constructs the multipliers.

`exists_middle` applies the existing integral genericity and multiplier existence theorems on the actual parity class of an arbitrary character pair. It chooses the representative `(c.parity.val+c'.parity.val)%2`, identifies it with `pairParity c c'`, and obtains a recurrent symmetric multiplier nonzero on that class. This avoids a restriction to the parity indices arising from `sd=se=0`.

Finally, `selectedParity` takes `sd=0` and `se=(P+M)%2`. Expanding the endpoint parities and using integer remainder arithmetic proves the compatibility hypothesis in `selectedParity_outer`, for every `d,e,k`. This is a choice of a presentation of the same two original induction blocks.

## Actual maps and the three source lists

For any compatible `sd,se` with `H>0`, the construction follows the ascending word

`[x,y,u,v] → [x,u,y,v] → [u,x,y,v] → [u,x,v,y] → [u,v,x,y]`.

The first and last crossings have binomial multipliers with cutoffs `P` and `H.toNat`. The two disjoint middle crossings are generic. Their composite `middle` is an exact intertwiner and is surjective: `middle_surjective` applies the inverse upper crossing followed by the inverse lower crossing and cancels both using the existing Fourier multiplier inverse identity.

The ordered source lists of the filtration are

1. `[.induced e,.induced d]`;
2. `outerPiece d e k sd se = [x,.induced (pairInduced u y P),v]`;
3. `innerPiece d e k sd se = [u,.induced (pairInduced v x H.toNat),y]`.

Endpoint characters here abbreviate `RealBlock.character`. `outerBinomial`, `outerSection`, `innerBinomial`, and `innerSection` are the actual Frobenius maps at the first and last crossings. The two decomposition lemmas apply the existing `RealInducedPairDistantFiltration.rankOne` with the displayed surrounding characters. Each section intertwines modulo its binomial range, and each binomial together with its section spans the full-character target. Exact Lie equivariance of the inverse-tail sections is not asserted. `innerBinomial_exact` proves exact equivariance of the last binomial using its positive cutoff, compatible parity and endpoint difference.

`first_eq`, `last_eq`, `crossings_eq`, and `beforeDescent_eq` identify the named composite with the four-crossing word followed by the actual target quotient. The existing ascending exchange descends that composite through the source quotient to an exact map from the swapped induction pair, with the same range. `filtration_of_pieces` then applies `RealInducedPairDistantFiltration.assemble`, together with its image-pushforward and spanning helpers. The three maps into the actual target are the descended map, the first section pushed through the middle crossings, last binomial and quotient, and the last section followed by the quotient. Each map intertwines modulo the preceding ranges; their ranges span the target. The lemma works with any predicate on these source lists.

## Support, weights and scope

`outer_support` and `inner_support` reuse the endpoint-support permutations, which are independent of internal parities. The squared-weight sums of the two fused lists are exactly `P²` and `H.toNat²`. The assumed strict bound forces `H>0`. Since `H+L+M=P` and both original weights are positive, `H.toNat<P`, so both fused lists are strictly heavier than `L²+M²`. The swapped source list supplies the other permitted kind of adjacent piece. `filtration` uses the selected parities, verifies these three allowed-piece conditions, and converts the resulting filtration through `realAdjacentFiltration_iff`.

For example, original weights `L=M=1`, exponents `0,5`, and `k=4` give `P=6`, `H=4` and the strict bound, while `P-M` is odd. The chosen internal parity is `se=1`, so this case is included by the new statement.

All content derives from the existing actual quotient, ascending exchange, rank-one binomial/tail decomposition, generic multiplier and support arithmetic constructions. No external source translation, classification premise, or unconditional filtration premise is used. Smaller positive inner weights, nonpositive inner weights, and zero original weights remain outside the stated region. No simultaneous two-window image identification is claimed.
