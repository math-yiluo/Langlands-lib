# The outer tail at a linked pair of real induction blocks

This internal derived construction gives an exact map out of the actual GL4 standard module with two induction blocks. It identifies its mixed target with the outer replacement datum already constructed in `RealInducedPairLinkedReplacement`, and computes its kernel inside the original source. It does not assert a filtration or an identification of the image with the two-block heavier replacement.

Write `a=d.exponent`, `b=e.exponent`, `L=|d.weight|`, `M=|e.weight|`, and suppose `IsLinkedAt d e k`, so `b-a=|L-M|/2+k+1`. Put `P=max(L,M)+k+1`. The canonical descending position characters of the original source are `[v,u,y,x]`, with exponents `[a+L/2,a-L/2,b+M/2,b-M/2]` and parities `[(L+1) mod 2,0,(M+1) mod 2,0]`. The additional parity assumption is `Even (P-M)`. This is the resonance condition for the central pair `(u,y)` in this canonical realization; it remains an explicit input. The result does not cover the other parity by an implicit change of model.

The difference `y.exponent-u.exponent` is `P`, and their pair induction is exactly `outerData d e k`, including its underlying complex character. Its exponent is `(a+b+(M-L)/2)/2`. The list `outerList` is `[character v,induced outerData,character x]`.

The actual central tail Frobenius map on the full four-character principal series has cutoff `P`, parity `pairParity u y`, and symmetry sign `(-1)^y.parity`. The proved rank-one tail construction supplies its induced target and exact compact and Lie equivariance. Define `outerMap` by first including the original two-induced-block space in that principal series, retaining both original Fourier constraints in its domain, applying this tail, and identifying its induction datum with `outerData`. The inclusion and the identification are exact, so `outerMap_exact` proves exact equivariance without any remaining landing premise.

Let `q` be the actual central binomial Frobenius map from `[v,y,u,x]` to `[v,u,y,x]`, with cutoff `P`. `full_kernel` proves that the full principal-series tail kernel is `range q`, using the proved rank-one binomial/tail kernel equality. Consequently `kernel` proves

```text
ker outerMap = (range q).comap inclusion.
```

The preimage is taken along the inclusion of the actual `[induced d,induced e]` standard module into the full four-character module. Thus the result keeps both original induction constraints. It neither replaces this intersection by an unrestricted binomial image nor assumes that every binomial output satisfies those constraints.

The additional theorem `outerMap_eq_zero_iff` says that a vector of the actual source belongs to this kernel precisely when all its position-one Fourier coefficients with `P <= |j|` vanish on the compact group. The proof cancels the tail multiplier on its nonzero parity class and uses the source parity to handle the other modes. The boundary `|j|=P` is absent from that parity class. The reverse implication uses the multiplier support and compact Fourier uniqueness in the actual mixed target.

`full_tail_section` also records the explicit inverse-tail section of the full principal-series tail. Its domain is the full mixed target. No claim is made that this section takes values in the original two-induced-block source. In particular, surjectivity of `outerMap`, nonvanishing of its image, a two-block description of that image, incoming heavier-piece maps, and the full `RealInducedInducedFiltrationStatement` remain separate obligations. Zero original weights are permitted by the stated construction, but no general zero-weight filtration is deduced here.

`RealInducedPairOuterTailStatement` packages exact equivariance of `outerMap` and the displayed restricted-kernel equality, universally quantifying the original data, linked index, linked equality and resonance parity. `realInducedPairOuterTail` proves it from the preceding lemmas.

The provenance is internal. The proof specializes the published rank-one tail and binomial constructions to the central pair of the actual descending GL4 principal series and combines them with the existing source inclusion and linked endpoint arithmetic. No external composition-series or classification assertion is used.

The exact source inclusion reuses the public
`RealInducedPairFrobenius.inclusion_intertwiner` from
`RealInducedPairIntertwiner`. The full-tail section reuses
`RealCharacterInducedPushforward.tail_inv`; the quotient-presentation
dependency retains its published version.
