# The heavier replacement pair for two real induction blocks

This derived arithmetic unit constructs a pair of actual induction-block parameters from the
four endpoints of two given blocks. It proves the support and weight conditions for an
allowed heavier piece of `RealAdjacentFiltration`. It does not construct an intertwining
operator, identify a subquotient, or prove that such a piece occurs in a filtration.

All new declarations are in
`Langlands.Archimedean.RealInducedPairLinkedReplacement`.

Write `a = d.exponent`, `b = e.exponent`, `L = |d.weight|`, `M = |e.weight|`,
`H = max(L,M)`, `S = min(L,M)`, and `t = k+1` for a natural number `k`.
Absolute weights are natural numbers; subtractions in the displayed formulas below are taken
in the integers or complex numbers, never truncated natural subtraction.

The definitions are

- `outerWeight = P = H+t`, `innerWeight = Q = t-S` (a signed integer);
- `outerExponent = u = (a+b+(M-L)/2)/2`;
- `innerExponent = v = (a+b+(L-M)/2)/2`;
- `outerData = characterOfParams P u`, `innerData = characterOfParams Q v`;
- `replacementPair = [induced outerData, induced innerData]`.

Here the published `characterOfParams` constructs the actual continuous complex character
with the specified integer weight and complex exponent. No parameter-existence assumption
is retained. Negative or zero `Q` is permitted; the standard-module support uses `|Q|`.

`IsLinkedAt d e k` is the complex equality
`b-a = |L-M|/2 + k+1`. Its Lean definition takes integer subtraction before `natAbs`,
then casts to the complex numbers. `linkedAt_iff` rewrites this as
`b-a = (H-S)/2 + k+1`.

Under this equality, `endpoint_equalities` proves

```text
u + P/2 = b + M/2,     u - P/2 = a - L/2,
v + Q/2 = b - M/2,     v - Q/2 = a + L/2.
```

The proof uses `H+S=L+M` and linear arithmetic over the complex numbers.
`signed_support` proves that the support of `characterOfParams Q v` is a permutation of
`[v+Q/2,v-Q/2]`, by splitting on the sign of `Q`. Appending the corresponding outer and
inner permutations and using the four endpoint equalities proves `support_perm`: the
replacement pair has exactly the original complex exponent support up to permutation.
This covers a zero inner weight and either ordering of the inner endpoints.

`weightSquareSum_gap` proves the exact integer identity

```text
W(replacementPair) - W([induced d, induced e]) = 2t(H-S+t),
```

where `W` is `realWeightSquareSum`. It uses `|Q|²=Q²`, and splits on `L≤M` to expand the
maximum and minimum. Since `t>0` and `H≥S`, the right side is positive.
`weightSquareSum_lt` therefore holds for every `d`, `e`, and `k`, without a linked-gap
hypothesis. `allowed_piece` combines this strict inequality with `support_perm` to supply
the heavier-piece alternative in the definition of `RealAdjacentFiltration`.
`isAdjacentPiece` packages the same result using `RealStandardFiltration.IsAdjacentPiece`
with arbitrary prefix and suffix lists.

The provenance is internal derivation from the published definitions of `realBlockSupport`,
`realExponentSupport`, `realBlockWeightSquare`, `realWeightSquareSum`, and
`RealStandardFiltration.IsAdjacentPiece`, together with `characterOfParams`. The formulas
come from pairing the two outer endpoints and the two inner endpoints of the original
four-element support. No external classification or composition-series result is used.
