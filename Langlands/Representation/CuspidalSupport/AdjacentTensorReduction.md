# Canonical tensor reduction for adjacent cuspidal induction

Author: Worker 289.

This internal construction uses the published small-universe cuspidal
factorization, canonical block-permutation tensor equivalence, normalized
induction of an equivalence, and transport of actual Jordan–Hölder series.
It does not prove the adjacent-swap theorem: the remaining canonical
product-matching assertion is an explicit proposition-valued input.

`canonicalCuspidalTensorData` accepts an irreducible cuspidal smooth source
representation of a positive-rank standard p-adic Levi, an arbitrary finite
permutation of its blocks, and an actual equivalence from its canonical
Weyl transport to a smooth target representation. It constructs:

- Supercuspidal representations of every source block, whose carriers lie
  in an independently prescribed universe.
- An actual equivalence from the source to their block tensor.
- An actual equivalence from the target to the block tensor reordered by
  the supplied permutation.

The source, target, factor-carrier and p-adic field universes are independent.
Target irreducibility and cuspidality are unnecessary for this construction.
The source factorization is supplied by
[`padicLeviCuspidalFactorization`](LeviTensorFactorizationProof.md).
Transport its resulting equivalence with `transportEquiv`, precompose with
the inverse of the given target equivalence, and postcompose with
[`blockPermutationTensorEquiv`](BlockPermutationTensor.md). All actions are
the actual product-Levi actions; inverse conjugation determines the direction.

`adjacentSwap_symm_val_eq_swap` identifies the finite adjacent transposition
with the natural-number transposition used by the published adjacent target.
`CanonicalAdjacentSupercuspidalProductMatchingStatement` states matching of
actual normalized product inductions of supercuspidal factors before and
after that transposition. It includes no assumed finite length or chosen
series, and this module supplies no proof of that assertion.

`adjacentBlockSwap_of_canonicalProducts` proves the exact published
`AdjacentBlockSwapCuspidalInductionFactorsTheorem` conditional on this
canonical product assertion. It uses
`eq_blockPermutation_of_blockIndex` to recover the canonical target shape
and actual coordinate permutation from minimality and the block labels.
The construction above then identifies both inducing representations with
the canonical tensors. Applying `normalizedParabolicInducedEquiv` to these
two identifications gives actual equivalences of the induced representations.
The shared `Langlands.haveSameJordanHolderFactors_transport` lemma in
[`JordanHolderTransportProof`](../Filtration/JordanHolderTransportProof.md)
maps the two composition series supplied by the
canonical matching through `jordanHolderSeriesTransport` and composes the
graded equivalences at each index. The same index permutation is retained,
so all multiplicities are retained. No extra finite-length assumption is
used in this transport.

The content is derived from the named Library results and the existing
definitions, without a new external-literature claim. The motivating
Bernstein–Zelevinsky adjacent-step context and its remaining
induction-in-stages obligations are recorded in
[`AdjacentSwapStatement`](AdjacentSwapStatement.md). In particular, the
canonical product input still requires the full two-block matching and
finite-length arguments; this conditional reduction does not discharge them.
