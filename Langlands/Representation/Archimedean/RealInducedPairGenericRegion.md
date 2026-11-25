# Filtrations outside the crossing resonance locus

This module connects the arithmetic crossing table in
`RealInducedPairResonance` with the proved generic exchange theorem in
`RealInducedPairGenericSwap`. It proves actual adjacent filtrations in the
regions specified below. The linked cases and the resonant cases at or below
the strict threshold remain outside these conclusions; the full
`RealInducedInducedFiltrationStatement` is proved separately, as
`realInducedInducedFiltration` in `RealInducedInducedFiltrationProof`.

All parameters `d,e` are arbitrary `ComplexCharacterData`, including weight
zero. Put `a=d.exponent`, `b=e.exponent`, `L=|d.weight|`, `M=|e.weight|` and
`h=halfWeightGap d e=(max(L,M)-min(L,M))/2`, with subtraction after complex
casts. The new helpers are in
`Langlands.Archimedean.RealInducedPairGenericRegion`.

`isGenericPair_iff_forall` identifies the four arithmetic crossing differences
and parities with the four conditions of
`RealInducedPairGenericSwap.IsGenericPair`. The proof expands
`swapParameter d e=a-L/2-b-M/2+1`; ring arithmetic gives:

| Crossing index | Parameter of the generic exchange |
| --- | --- |
| 0 | `swapParameter-1` |
| 1 | `swapParameter-1+L` |
| 2 | `swapParameter-1+M` |
| 3 | `swapParameter-1+L+M` |

At each index the reduced parity is definitionally the same as in the generic
exchange predicate. Splitting the four indices therefore identifies its four
conjuncts. Classical logic then gives `isGenericPair_iff_not_resonant`:
genericity is equivalent to the negation of `HasCrossingResonance d e`.

`isGenericPair_of_not_integer_coset` uses the already proved implication

```text
HasCrossingResonance d e -> exists q : Int, b-a=h+q.
```

Thus the absence of such an integer `q` gives genericity.
`isGenericPair_of_im_ne` obtains this absence from `im(a) != im(b)` by taking
imaginary parts: `h` and every integer have imaginary part zero.
Neither implication needs an inequality between the real parts.

Under the explicit strict hypothesis `re(h)<re(b)-re(a)`, the imported
`resonance_iff_exists_linkedAt` identifies resonance with a natural linked
index. Negating this equivalence proves
`isGenericPair_iff_no_linked_above_threshold`:

```text
re(h)<re(b)-re(a) ->
  (IsGenericPair d e <-> forall k : Nat, not (IsLinkedAt d e k)).
```

The strict threshold is retained throughout. Absence of a linked index alone
is not asserted to imply genericity at smaller positive gaps.

`filtration_of_not_integer_coset`, `filtration_of_im_ne` and
`filtration_of_no_linked_above_threshold` apply the published
`RealInducedPairGenericSwap.filtration` to these three genericity results.
Their conclusion is the actual
`RealAdjacentFiltration 4 [] [] (induced d) (induced e)`.
The imported proof constructs a bijective exact intertwiner, inverts it and
pushes the exchanged module's identity filtration along that inverse. Its
single piece is `[induced e,induced d]`; this module adds only the arithmetic
sufficient conditions and reuses that construction without additional map
or occurrence premises.

`Langlands.Archimedean.RealInducedPairNonlinkedAboveThresholdFiltrationStatement`
records the third conclusion with precisely the strict threshold and the
absence of every natural linked index as hypotheses.
`realInducedPairNonlinkedAboveThresholdFiltration` proves this proposition.
No nonzero-weight or real-part-order premise is added.

The provenance is internal: the proved crossing coset and linkedness
criteria, the actual four-crossing parameter definition and the proved
generic exchange filtration. The proof uses ring identities, finite case
analysis, classical negation, imaginary parts and the imported implications.
No external literature or classification result is used.
