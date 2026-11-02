# Pointwise Jacquet coefficient cancellation

Module `Langlands.Group.RelativeWeylJacquetProof`, namespace
`Langlands.Group.RelativeWeylIndexing`. The proof combines Worker 1230's
Boolean calculation with Worker 1254's intrinsic image-coverage argument.

## Exact target and scope

`jacquetCancellation_proof` has type `jacquetCancellation cs`, the proposition
defined in `Langlands.Group.RelativeWeylIndexingTargets`. Its parameters are
independent universes `B : Type u` and `W : Type v`, `[Group W]`,
`M : CoxeterMatrix B`, `cs : CoxeterSystem M W`, `[Fintype B]`, and
`[Fintype W]`. Write `s_i = cs.simple i`, `ℓ = cs.length`, and
`P = positiveSimpleSet cs w = {i | ℓ(w) < ℓ(w s_i)}`.

For every `J`, every `w` satisfying `IsMinimal cs J ∅ w`, and every `K ⊆ J`,
the theorem proves the integer identity

```text
∑ I ∈ P.powerset,
  (if simpleImage cs w I ∩ J = K then (-1)^|I| else 0)
  =
if MapsIntoSimple cs w P J then (-1)^|K| else 0.
```

The minimality condition is on the left coset `W_J w`. The sum includes every
subset of `P`, and its condition retains the exact intersection with `J`.
`MapsIntoSimple` universally requires, for every `i ∈ P`, some `j ∈ J` with
`w s_i w⁻¹ = s_j`. An index whose conjugate is not simple therefore makes the
condition false. The theorem adds no coverage, injectivity, longest-element,
root-realization, or representation-theoretic premise. Empty `B`, `J`, or `K`
and full subsets remain included.

## Provenance

This is an internal proof of the published target, whose original-source
locator is Aubert 1995, `aubert-1995-duality`, SHA-256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
printed p.2182, the coefficient calculation in (1.9). The argument here
derives the target from the Coxeter presentation, length and exchange
theorems, finite subsets, and integer arithmetic. It does not claim to
follow the source's proof route.

As in the target, `positiveSimpleSet` uses length increase and `simpleImage`
uses conjugation of reflections. Passing to actual relative roots, root
signs, Levi subgroups, or Jacquet functors requires separate comparisons.
Those interpretations are not part of this theorem.

## Boolean calculation

`jacquet_sum_zero_of_not_maps` works with any finite domain `P` and does not
assume simple-reflection injectivity or minimality. Failure of `MapsIntoSimple`
supplies `i ∈ P` with no simple image in `J`. Inserting `i` in any subset
leaves its image intersection with `J` unchanged:
`simpleImage_insert_bad` proves this directly by membership. The powerset
sum splits into subsets of `P.erase i` and the same subsets with `i`
inserted. Insertion increases cardinality by one, so the two sums are
negatives and cancel.

`jacquet_sum_of_maps_and_coverage` assumes simple-reflection injectivity,
`MapsIntoSimple cs w P J`, and `simpleImage cs w P = J`. For `K ⊆ J`,
define `Q ⊆ P` by retaining the indices whose conjugate is a simple
reflection indexed by `K`. Coverage gives `simpleImage cs w Q = K`.
Injectivity of the simple labels and of conjugation proves that, among
`I ⊆ P`, the condition `simpleImage cs w I ∩ J = K` is equivalent to
`I = Q`. A finite bijection between `Q` and `K` proves `Q.card = K.card`.
The sum therefore has exactly one nonzero term, equal to `(-1)^K.card`.

## Intrinsic coverage

`subset_simpleImage_of_mapsIntoSimple`, contributed by Worker 1254, proves
coverage from the hypotheses of the true branch of the target. It uses no
injectivity premise.

1. `minimalityLengthCriterion_proof` gives `ℓ(w) < ℓ(s_j w)` for every
   `j ∈ J`. `left_minimal_of_simple` gives `ℓ(w) ≤ ℓ(a w)` for all
   `a ∈ W_J`.
2. `exists_full_descent_of_mapsIntoSimple` supplies `a ∈ W_J` for which
   `y = a w` has every simple reflection as a right descent.
3. For `j ∈ J`, set `r = w⁻¹ s_j w`. The full-descent suffix theorem
   `exists_suffix_of_full_descent` gives `y = z r` and
   `ℓ(y) = ℓ(z) + ℓ(r)`. Group cancellation identifies `z = a s_j w`.
4. Since both `a` and `a s_j` belong to `W_J`, left-minimal length
   additivity gives `ℓ(a w) = ℓ(a) + ℓ(w)` and
   `ℓ(a s_j w) = ℓ(a s_j) + ℓ(w)`. Together with
   `ℓ(a) ≤ ℓ(a s_j) + 1`, these equalities imply `ℓ(r) ≤ 1`.
5. The element `r` is nonidentity, since otherwise `s_j = 1`, contradicting
   `ℓ(s_j) = 1`. Thus `ℓ(r) = 1`, so `r = s_i` for some simple index.
   It follows that `w s_i w⁻¹ = s_j`. Moreover `w s_i = s_j w`,
   so the strict inequality from step 1 proves `i ∈ P`.

Consequently every `j ∈ J` lies in `simpleImage cs w P`. In the final proof,
`MapsIntoSimple` and the intrinsic theorem `simple_reflection_injective`
give the opposite inclusion: if a conjugate equals both `s_j` and a
simple reflection indexed by `J`, injectivity identifies those labels.
This supplies the coverage equality required by the Boolean calculation.
The final theorem splits on `MapsIntoSimple` and applies the corresponding
Boolean lemma.

## Actual dependencies

The module imports:

- `Langlands.Group.RelativeWeylLongestSurvivorProof`, for
  `exists_full_descent_of_mapsIntoSimple`,
  `exists_suffix_of_full_descent`, and `mem_positiveSimpleSet`. Its imports
  provide the published minimality criterion, one-sided length additivity,
  exchange, the indexing definitions, and the unchanged target.
- `Langlands.Group.RelativeWeylSimpleInjective`, for
  `simple_reflection_injective`. That theorem derives injectivity from a
  finite-rank complex reflection representation, with no finiteness
  requirement on `W` and no faithfulness assumption.
- `Mathlib.Algebra.BigOperators.Group.Finset.Powerset`, for the insertion
  decomposition of the powerset sum and finite-sum arithmetic.

The coverage proof uses the full-descent helpers from the first import; it
does not invoke `longestSurvivor_proof` or assume any sibling target.
The remaining Coxeter facts are Mathlib's simple-reflection cancellation,
length subadditivity, length-zero characterization, and length-one
characterization. The implemented internal lemmas prove the entire
coverage and Boolean calculation; none of these conclusions is retained
as an extra premise of `jacquetCancellation_proof`.
