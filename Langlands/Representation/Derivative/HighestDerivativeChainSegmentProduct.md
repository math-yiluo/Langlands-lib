# Derivative chains of subobjects of ordered segment products

These are derived proof lemmas for the irreducibility assertion in Zelevinsky (1980),
Theorem 8.1. The inputs use actual product data `c` with segment socles and the order
condition that no earlier segment precedes a later one. Write `a = c.multisegment`
and `k` for the sum of the ranks of the cuspidal bases of its segments. The chain in
both induction lemmas is `levelSequence a` from `HighestDerivativeChain`.

## One step

For nonempty `a`, `segmentProduct_step` gives `0 < k ≤ n`, ordered product data `c'`
on `GL_(n-k)` for `a.filterMap Segment.dropLast`, and an isomorphism from the order-`k`
derivative of `c.induced` to `c'.induced`. It also gives vanishing of all higher
feasible derivatives of `c.induced` and nonvanishing at order `k` for every nonzero
smooth subrepresentation of `c.induced`. The proof uses the published product derivative
calculation (§6.6), preservation of the precedence order under truncation, and the
homogeneity theorem (Theorem 6.2). For the last assertion, the mirabolic restriction
of a nonzero subrepresentation has the same level as the homogeneous restriction of
the product, whose level is `k` by the derivative calculation.

## Quotients and pairings

- `not_derivativeChain_of_quotient`: for a short exact sequence `K → V → W` with
  `K` nonzero and `V` embedded in `c.induced`, the chain of `W` fails. If `a` is empty,
  `c` has rank zero and its product has dimension one. A nonzero `K` then fills `V`,
  and `W` is zero. Otherwise the first order in the chain is `k`. Exactness gives
  a short exact sequence of derivatives, the order-`k` derivative of `K` is nonzero
  by homogeneity, and the derivative of `V` embeds in the truncated product. Apply
  the induction hypothesis at the smaller rank to the remaining orders.
- `derivativeChain_of_pairing`: if a nonzero `A` embeds in `c.induced` and has an
  invariant bilinear pairing with `B` nondegenerate in `A`, then the chain of `B`
  holds. For the empty chain, the pairing forces `B` to be nonzero. Otherwise `A`
  has highest order `k` by the one-step lemma and exactness. Twist `B` by `|det|`
  to give the pairing the required covariance on restriction to the mirabolic.
  The highest-derivative pairing theorem then gives an invariant pairing at order
  `k`, nondegenerate in the derivative of `A`. This derivative is nonzero and embeds
  in the truncated product. Induct on rank and use determinant-twist invariance of
  the chain to return to the original `B`.

The last step uses the published `mirabolicHighestDerivativePairing`, formalizing
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I* (1977),
Proposition 3.8, p. 453 (`bernstein-zelevinsky-1977-induced-i`). The product and
homogeneity inputs are from A. V. Zelevinsky, *Induced representations of reductive
p-adic groups II* (1980), Theorem 6.2 and §6.6 (`zelevinsky-1980-induced-ii`). The two
chain lemmas are auxiliary inductions proved here, not statements attributed to those
sources.
