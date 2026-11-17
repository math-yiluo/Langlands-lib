# Linked filtration from singular middle crossings

This internally derived supporting result proves an actual adjacent filtration of two real induction blocks in a larger linked region. It does not prove the unconditional `RealInducedInducedFiltrationStatement`.

For complex character data `d,e` and a natural linked-gap index `k`, write `L=d.weight.natAbs`, `M=e.weight.natAbs`, `P=outerWeight d e k=max L M+k+1`, and `H=innerWeight d e k=k+1-min L M`, with `H` an integer. `RealInducedPairMiddleParityFiltrationStatement` states that `L>0`, `M>0`, `IsLinkedAt d e k`, and `L²+M²<(k+1)²` imply the actual `RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)`. The theorem `realInducedPairMiddleParityFiltration` proves this proposition. There is no canonical parity hypothesis.

For example, original weights `L=M=2`, exponents `0,3`, and `k=2` give `P=5`, `H=1`, and `8<9`. These parameters satisfy the new size hypothesis but do not satisfy the earlier distant-region condition `L²+M²<H.toNat²`.

## Weights and compatible internal parities

The actual quotient presentation permits arbitrary internal parities `sd,se : Fin 2`. Set `u=lo d sd`, `v=hi d sd`, `x=lo e se`, and `y=hi e se`. These are ascending endpoint characters for the original two blocks, whose data are unchanged by the internal choices. Define the natural middle weights

- `lowerWeight d e k = P-M`;
- `upperWeight d e k = P-L`.

`weight_id` proves their integer identities `A=H+L` and `B=H+M`. `gap_le` proves `k+1≤A` and `k+1≤B`; in particular both weights are positive for every natural linked index, regardless of the sign of `H`. `lower_difference` and `upper_difference` identify them with `x.exponent-u.exponent` and `y.exponent-v.exponent`.

The temporary parity condition is `Even ((P : ℤ)-pairParity u y)`. In contrast with the distant construction, this makes the outer and inner crossings generic. `parities` proves the reducible parities for the two middle weights and the generic parity for the signed inner weight. `exists_ascendingData` obtains recurrent symmetric generic multipliers for the first and last crossings, nonzero on their actual parity classes, and uses the binomial multipliers for the middle crossings. It applies `RealInducedPairDistantParity.exists_middle` to the outer and inner endpoint pairs; that helper handles signed integral differences as well as positive ones. No positivity assumption on `H` is needed for this construction.

`selectedParity` chooses `sd=0` and `se=(P+M+1)%2`. Expanding the actual endpoint parities proves the temporary parity condition in `selectedParity_outer`. This is a choice of a quotient presentation of the same original two induction blocks, with no restriction on the original canonical parity.

## Maps and assembly

The ascending word is

`[x,y,u,v] → [x,u,y,v] → [u,x,y,v] → [u,x,v,y] → [u,v,x,y]`.

Its first and last maps are generic. The two middle maps are `lowerBinomial` and `upperBinomial`, at weights `A` and `B`. Their rank-one sections, `lowerSection` and `upperSection`, have source lists

1. `lowerPiece d e k sd se = [.induced (pairInduced u x A),y,v]`;
2. `upperPiece d e k sd se = [u,x,.induced (pairInduced v y B)]`.

Endpoint characters in these lists abbreviate `RealBlock.character`. The decomposition lemmas apply `RealInducedPairDistantFiltration.rankOne` with the indicated surrounding characters. Each section intertwines modulo its binomial range, and the binomial and section together span the appropriate four-character space. `upperBinomial_exact` supplies exact intertwining for the second middle binomial.

`inverseFirst` is the Frobenius map with the pointwise inverse first multiplier. The generic nonvanishing proves `first_inverse` and hence surjectivity of the first crossing. The same cancellation argument proves `last_surjective`. The inverse is used here as a linear section; no additional Lie-intertwining claim about it is needed.

Let `Q` be the actual target tail quotient and `Amap=Q ∘ lastCrossing`. Both factors are surjective exact intertwiners. The published ascending exchange theorem descends the entire word followed by `Q` to an exact map `q` from `[.induced e,.induced d]` to the original target, with the stated factorization and equality of ranges. `crossings_eq` identifies the middle binomials in that word. Composing the source quotient with `inverseFirst` gives a linear map `π` for which

`q ∘ π = Amap ∘ upperBinomial ∘ lowerBinomial`.

Surjectivity of the first crossing also identifies `range q` with the range of that latter composite. These are precisely the two descent identities required by the existing `assemble` lemma. The resulting three ordered maps into the actual target have sources `[.induced e,.induced d]`, `lowerPiece`, and `upperPiece`. Each intertwines modulo the preceding ranges, and the three ranges span the target. `filtration_of_pieces` establishes this construction for any predicate on those three source lists. It works for every signed inner weight with positive original weights and compatible internal parities; the final size bound is used only to make the two fused lists allowed adjacent pieces.

## Endpoint support and final bound

The lower fused list has exponent support `[x.exponent,u.exponent,y.exponent,v.exponent]`; the upper fused list has support `[u.exponent,x.exponent,y.exponent,v.exponent]`. The support lemmas compute these lists from the actual endpoint differences and exhibit permutations to the original support `[v.exponent,u.exponent,y.exponent,x.exponent]`. These calculations do not depend on internal parities. The respective squared-weight sums are exactly `A²` and `B²` because the remaining blocks are characters.

The assumption `L²+M²<(k+1)²`, together with `k+1≤A,B`, makes both fused lists strictly heavier than the original pair. The exchanged source is the other permitted adjacent piece. `filtration` uses the selected parities, supplies these three allowed-piece conditions, and applies `realAdjacentFiltration_iff` to obtain the exact stated proposition.

This is a derivation from the existing quotient presentation, rank-one binomial/tail decomposition, signed-integral generic multiplier existence, ascending exchange descent, finite three-map assembly, and endpoint arithmetic. It introduces no literature translation or classification premise. The remaining linked region `L²+M²≥(k+1)²`, zero original weights, and the unconditional two-induction-block theorem are not settled by this statement. In particular, the combined squared weights of two simultaneous fused blocks do not justify discarding either single-fused source list; no such elimination or simultaneous-window image identification is asserted here.
