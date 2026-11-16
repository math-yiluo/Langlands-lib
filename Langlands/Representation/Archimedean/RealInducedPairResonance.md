# Crossing resonance and the positive linked-gap threshold

This derived arithmetic unit compares the four character crossings of two real
induction blocks with their original diagonal positions. It proves that, above
an explicit gap threshold, a crossing resonance is equivalent to a positive
linked-gap index. It then applies the linked replacement's support and weight
theorems. It supplies no intertwining operator, kernel map, representation
occurrence, spanning theorem or proof of the full filtration statement.

All new declarations are in
`Langlands.Archimedean.RealInducedPairResonance`.
The parameters `d` and `e` are arbitrary `ComplexCharacterData`; there is no
nonzero-weight assumption.

Write `a = d.exponent`, `b = e.exponent`, `z = b-a`,
`L = |d.weight|`, `M = |e.weight|`, `H = max(L,M)` and `S = min(L,M)`.
Absolute weights are natural numbers. Differences such as `L-M` and `H-S`
below are taken after casting to the integers or complex numbers.
`halfWeightGap d e` is the complex number `(H-S)/2`.

`crossingDifference`, `crossingParity`, `crossingPositions` and `crossingOffset`
are functions on `Fin 4`, in the following order:

| Index | Original positions | Unshifted difference | Reduced parity | Integer offset |
| --- | --- | --- | --- | --- |
| 0, first | (1,2) | `-z-(L+M)/2` | `(M+1)%2` | `-H` |
| 1, left middle | (0,2) | `-z+(L-M)/2` | `(L+M+2)%2` | `L-H` |
| 2, right middle | (1,3) | `-z+(M-L)/2` | `0` | `M-H` |
| 3, last | (0,3) | `-z+(L+M)/2` | `(L+1)%2` | `S` |

The parities take their values in the integers, with representatives zero or
one. `crossingDifference_eq_position` proves that each difference is the first
original position exponent minus the second original position exponent, using
`GramFormula.realPositionExponent [induced d, induced e]`.
`crossingParity_eq_position` proves that each parity is the sum of the two
original `RealBlockPosition.realPositionSign` values modulo two.
The proofs expand the four positions, then use ring arithmetic for exponents
and natural-number modular arithmetic for signs. These comparisons concern
the original position characters; no transformed representation is constructed.

`HasCrossingResonance d e` is the proposition that at least one of these four
differences fails `RealBlockMultiplier.IsGenericParameter` with its corresponding
parity. The imported predicate excludes both
`epsilon+2m+1` and `-(epsilon+2m+1)` for every natural `m`.

`crossingDifference_eq` establishes, at each index,

```text
crossingDifference = halfWeightGap - z + crossingOffset.
```

Its proof uses `H+S=L+M` and linear combinations over the complex numbers.
Failure of `IsGenericParameter` makes the difference an integer: the private
helper `exists_int_of_not_generic` extracts one of the two excluded integer
values. Subtracting that value from the integer offset proves
`gap_eq_halfWeightGap_add_int`:

```text
HasCrossingResonance d e ->
  exists q : Int, z = halfWeightGap d e + q.
```

`exists_linkedAt_of_resonance` additionally assumes
`re(halfWeightGap d e) < re(b)-re(a)`. Taking real parts gives `q>0`.
The proof chooses `k=(q-1).toNat`, so `q=k+1`, and applies the linked replacement's
`linkedAt_iff`. Thus its conclusion is `exists k : Nat, IsLinkedAt d e k`.
This is the full complex linked-gap equality, not merely an equality of real
parts.

Conversely, `crossingDifference_of_linked` rewrites every difference at a linked
gap as `crossingOffset-k-1`. `hasCrossingResonance_of_linked` proves that at least
one crossing is resonant. The private helper `not_generic_neg_nat` shows that
`-r` is singular for a reduced parity `epsilon` when `r>0` and
`r%2=(epsilon+1)%2`, by writing
`r=epsilon+2*((r-epsilon-1)/2)+1`.
If `L<=M`, the proof uses the right middle crossing when `k` is even and the
first crossing otherwise. If `L>M`, it uses the left middle crossing when
`k%2=(L+M+2)%2` and the first crossing otherwise. All cases meet that helper's
positivity and parity conditions. The converse has no threshold premise.

`resonance_iff_exists_linkedAt` combines the two implications under the strict
threshold hypothesis. `exists_heavier_piece_of_resonance pre post` then supplies
a linked index together with the linked replacement's support permutation,
strict increase of `realWeightSquareSum`, and
`RealStandardFiltration.IsAdjacentPiece` conclusion in arbitrary surrounding
lists. The support, weight and adjacent-piece proofs are reused from
`RealInducedPairLinkedReplacement`; no occurrence claim is added.

The strict threshold cannot be replaced just by `re(a)<re(b)`.
`resonance_below_threshold` proves a concrete counterexample with
`d=characterOfParams 6 0` and `e=characterOfParams 1 (1/2)`.
Here the left middle difference is `2` with parity `1`, so it is singular.
The exponent gap is positive but equals `1/2`, below the threshold `5/2`.
For every natural `k`, `IsLinkedAt d e k` would force
`1/2=5/2+k+1`, which is impossible. This theorem asserts those four properties;
it does not assert vanishing of any operator.

The provenance is internal derivation from the published position exponents,
position signs, `IsGenericParameter`, actual-character constructor
`characterOfParams`, and the linked replacement definitions and arithmetic.
The four original crossing pairs give the displayed table; the common integer
coset, positivity and parity computations give the proved implications. No
external literature or classification premise is used.
