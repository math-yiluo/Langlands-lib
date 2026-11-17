# Filtration for sufficiently distant linked real induction blocks

This is an internal derived result for the actual `O(4)`-finite standard modules. It proves the adjacent filtration in a specified region of linked parameters. It does not prove the unconditional `RealInducedInducedFiltrationStatement`.

For complex character data `d,e` and a natural linked-gap index `k`, put

- `L = d.weight.natAbs`, `M = e.weight.natAbs`;
- `P = outerWeight d e k = max L M + k + 1`;
- `H = innerWeight d e k = k + 1 - min L M`, an integer.

`RealInducedPairDistantFiltrationStatement` quantifies over all `d,e,k`. Its assumptions are `L>0`, `M>0`, `IsLinkedAt d e k`, the canonical resonance parity `Even(P-M)`, and `L²+M² < H.toNat²`. Its conclusion is the actual `RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)`. The last inequality forces `H>0`. The assumptions are compatible: weights `L=M=1`, exponents `0,4`, and `k=3` give `P=5`, `H=3`, and the required parity and strict inequality. The linked equality itself implies the ascending real-exponent order. The theorem `realInducedPairDistantFiltration` proves this exact proposition.

## The three source lists

Write `u=lo d 0`, `v=hi d 0`, `x=lo e 0`, `y=hi e 0` for the ascending endpoint characters in `RealInducedPairQuotientPresentation`. The finite filtration uses the following source lists, in order:

1. `[.induced e, .induced d]`;
2. `outerPiece d e k = [x, .induced (pairInduced u y P), v]`;
3. `innerPiece d e k = [u, .induced (pairInduced v x H.toNat), y]`.

The notation for endpoint characters in these lists abbreviates `RealBlock.character`. Each map goes into the original actual standard module `[.induced d,.induced e]`. Equivariance for each map is modulo the sum of the preceding ranges; the sum of all three ranges is the full module. Neither individual nonzero maps nor an irreducible composition series are asserted.

## Implemented proof

`rankOne` works with arbitrary surrounding lists. For an ascending character pair with positive integral difference and the reducible parity, let `Q` be its reversed-pair binomial map, `D` its tail map, and `S` the inverse-tail Frobenius map from the fused induction block. The published tail-inverse identity gives `D S = id`. The tail kernel lies in `range Q`, so `f-S(D f)` is a binomial image. Thus every target vector is `Q z+S r`. Since `D` is an exact intertwiner, its left inverse `S` intertwines modulo `range Q`. This proves both claims of `rankOne`; it does not assert exact equivariance of the inverse-tail section.

`differences` computes the four incoming ascending differences as `P,H+L,H+M,H`. `upper_parity`, `outer_parity`, `inner_parity`, and `inner_difference` supply the actual reduced parities and natural inner cutoff. `exists_ascendingData` constructs the word

`[x,y,u,v] → [x,u,y,v] → [u,x,y,v] → [u,x,v,y] → [u,v,x,y]`.

The first and last crossings have binomial multipliers at `P` and `H.toNat`. The middle crossings have integral generic parameters with the same parity as their parity indices, and their multipliers are nonzero on exactly the actual parity classes. Their composite is `middle`. `middle_exact` proves exact intertwining. `middle_surjective` constructs a right inverse by applying the inverse of the upper crossing and then the inverse of the lower crossing; the published Frobenius inverse identity verifies the cancellation.

`outer_decomposition` applies `rankOne` at the first crossing, with surrounding lists `[x]` and `[v]`. `inner_decomposition` applies it at the last crossing, with surrounding lists `[u]` and `[y]`. Their maps are `outerBinomial`, `outerSection`, `innerBinomial`, and `innerSection`; `innerBinomial_exact` gives exact equivariance of the last binomial.

Let `A` be the actual split quotient from `[u,v,x,y]` to `[.induced d,.induced e]`, `B=middle`, and let `G` be the last binomial. The four-crossing word followed by `A` descends, by the published ascending exchange theorem, through the source quotient `[x,y,u,v] → [.induced e,.induced d]`. The descended map `q` is exact, factors the full-character composite, and has the same range. `first_eq`, `last_eq`, `crossings_eq`, and `beforeDescent_eq` explicitly identify these composites.

The abstract `assemble` lemma uses those factorization and range identities. If `F=B outerBinomial`, `s=B outerSection`, and `t=innerSection`, the two decompositions say that `F` and `s` span the middle target and that `G` and `t` span the final four-character target. Surjectivity of `B` supplies the first of these spanning statements. The three resulting maps are `q`, `A G s`, and `A t`. Composition carries the section's equivariance modulo an image to equivariance modulo the image's pushforward. The first spanning identity places `range(A G)` inside the first two ranges; the second and surjectivity of `A` prove total spanning. `modulo_comp_range` and `span_comp` package the two elementary transport steps, and `filtration_of_pieces` applies this assembly to the actual maps for any predicate on source lists.

Finally, `outer_support` and `inner_support` calculate the fused endpoint supports and exhibit permutations of the original four endpoints. The squared weights of the fused lists are exactly `P²` and `H.toNat²`. The identity `P=H+L+M` and positivity give `H.toNat<P`, so the assumed inner bound makes both lists strictly heavier than the original sum `L²+M²`. The swapped source list is the other permitted kind of adjacent piece. `filtration` applies `realAdjacentFiltration_iff` to obtain the stated adjacent filtration.

## Provenance and scope

All content is derived from the existing standard-module, Fourier/Frobenius, rank-one tail, actual quotient, and ascending-exchange constructions. `RealInducedPairLinkedIncoming` supplies weight arithmetic and integral genericity helpers, rather than an assumption of a filtration or a classification theorem. There is no additional source assertion or literature translation in this module.

The full two-induction-block task still includes smaller positive inner weights, nonpositive signed inner weights, noncanonical parity, and zero original weights. This result settles only the region with the explicit assumptions above. It needs no identification of the simultaneous two-window incoming image and makes no such identification.
