# Filtration at the zero inner-weight boundary

This internally derived result proves the actual adjacent filtration when both original induction weights are positive and the signed inner weight is zero. It imposes no canonical parity hypothesis and no additional size bound. The unconditional two-induction-block theorem remains open outside the proved regions.

For complex character data `d,e` and a natural linked index `k`, write `L=d.weight.natAbs`, `M=e.weight.natAbs`, `P=outerWeight d e k`, and `H=innerWeight d e k`. `RealInducedPairZeroInnerFiltrationStatement` states that `L>0`, `M>0`, `IsLinkedAt d e k`, and `H=0` imply `RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)`. The theorem `realInducedPairZeroInnerFiltration` proves this exact proposition. For example, `L=M=1`, exponents `0,1`, and `k=0` satisfy the hypotheses; the canonical condition `Even(P-M)` fails in this example and is not required here.

## Genericity at zero

For any pair of real characters, `exists_zero` constructs a recurrent symmetric multiplier at exponent difference zero, nonzero on the actual parity class. Zero avoids every positive and negative singular value `±(epsilon+2*m+1)` for either reduced parity `epsilon`. The proof takes real parts and uses positivity to establish genericity, then applies the existing generic multiplier existence theorem. In particular, zero is treated by a generic multiplier, rather than by a binomial of cutoff zero.

Choose the free internal quotient parities `sd,se` and let `u=lo d sd`, `v=hi d sd`, `x=lo e se`, and `y=hi e se`. The temporary compatibility condition is `Even ((P : ℤ)-1-pairParity u y)`. The identity `H+L+M=P` and `H=0` make the two middle differences `L,M` generic on their actual parity classes. The last difference `x.exponent-v.exponent` is zero, so `exists_zero` handles its parity without an additional assumption.

`exists_ascendingData` therefore supplies the actual ascending word

`[x,y,u,v] → [x,u,y,v] → [u,x,y,v] → [u,x,v,y] → [u,v,x,y]`.

The first crossing has binomial multiplier at `P`. The two disjoint middle crossings and the final zero-difference crossing are generic and nonvanishing on their parity classes.

## Two-piece construction on the actual target

The map `suffix` comprises the last three crossings. `suffix_exact` composes their exact intertwining statements. `suffix_surjective` uses the two middle inverse maps already constructed in `RealInducedPairDistantParity` and the pointwise inverse of the final generic multiplier. The existing Fourier multiplier cancellation identity verifies the latter inverse. Thus the suffix is onto the final four-character space.

Let `Q` be the actual split tail quotient from `[u,v,x,y]` to `[.induced d,.induced e]`, and set `A=Q ∘ suffix`. This is an exact surjective intertwiner. At the first crossing the existing rank-one decomposition gives an outer binomial `F` and an inverse-tail section `S` from

`outerPiece d e k sd se = [x,.induced (pairInduced u y P),v]`.

The section intertwines modulo `range F`, and every vector of `[x,u,y,v]` is `F z+S r`.

The published ascending exchange theorem descends the full word followed by `Q` to an exact map `q` from `[.induced e,.induced d]` to the original actual target. `first_eq`, `crossings_eq`, and `beforeDescent_eq` identify its full-character composite with `A ∘ F`. The descent theorem gives both `q ∘ sourceQuotient=A ∘ F` and `range q=range(A ∘ F)`.

Consequently `A ∘ S` intertwines modulo `range q`. Surjectivity of `A` and the rank-one spanning identity express every actual target vector as `q w+(A ∘ S) r`. The existing two-piece assembly lemma then gives a filtration with ordered source lists `[.induced e,.induced d]` and `outerPiece`. `filtration_of_pieces` proves this for any predicate accepting these two lists. No identification of a two-window inverse image or actual outer-map range is assumed.

## Parity selection and allowed sources

The final proof uses `sd=0` and `se=RealInducedPairDistantParity.selectedParity d e k`, whose value is `(P+M)%2`. The existing parity computation proves the temporary compatibility condition. These are choices of presentation of the same original induction data.

The existing outer-support computation shows that the fused source preserves the original four endpoints up to permutation. Its squared-weight sum is `P²`. From `H=0` the weight identity gives `P=L+M`, and positivity of both original weights implies `L²+M²<P²`. The outer source therefore meets the heavier-piece alternative. The exchanged pair meets the other allowed alternative. Applying `realAdjacentFiltration_iff` proves the stated actual adjacent filtration.

All mathematical inputs are the existing actual quotient and ascending exchange, generic multiplier existence and inverse identities, the rank-one section modulo a binomial image, and endpoint support arithmetic. No Langlands classification, composition-series theorem, translation functor or unconditional filtration result is used. The statement still assumes positive original weights and exactly zero signed inner weight; it asserts neither a surjective actual outer map nor a full incoming image-kernel equality.
