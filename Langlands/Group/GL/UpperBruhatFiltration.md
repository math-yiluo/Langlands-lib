# Inversion layers of actual upper Bruhat cells and the transpose index

Author: Worker 781.

This pair supplies a finite combinatorial interface on the actual upper Bruhat
cells published in `Langlands.Group.GL.UpperBruhatCells`. It defines the
inversion count of a permutation, the unions of cells bounded by that count, the
"strictly higher" unions and the cell neighborhoods, and the permutation index
used for transpose. All declarations are in `Langlands.GeneralLinear`. They hold
for every natural rank `n`, including zero. The set constructions work over every
commutative ring `R` in an arbitrary universe, so they specialize directly to
every field. No topology, positivity, nontriviality or field hypothesis appears.
The imported pairs `Langlands.Group.GL.UpperBruhatCells` and
`Langlands.Combinatorics.RelationInversions` are used unchanged.

## Source and provenance

The registered original is `shalika-1974-multiplicity-one`, J. A. Shalika,
*The multiplicity one theorem for GLn*, Ann. of Math. (2) 100 (1974),
171–193. The retained file is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
with SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Printed pp.174–175 and 178–179 (one-based PDF pages 5–6 and 9–10) were read and
visually checked. No source-specific errata file was found in the project or
Library notes.

On printed p.174 the double cosets are `G_w = HUwU`, where `H` is the diagonal
subgroup and `U` is the upper unipotent subgroup, so `HU` is the upper triangular
subgroup. The imported `upperBruhatCell n R w` is this actual double coset for the
published permutation matrix. The same page defines the anti-automorphism
`θ(x) = w₀ h₀ ᵗx h₀⁻¹ w₀⁻¹`. The Corollary on printed p.175 defines `Ω_w` as the
union of `G_w` with the double cosets of strictly larger dimension. On printed
p.178, Shalika lists the dimensions `r₀ = -1 < r₁ < ... < r_N` of the double
cosets, including the empty set. The source lets `ω_j` be the union of the
double cosets of dimension `≤ r_j`. Lemma 1.16 and the proof of Theorem 1.6 on printed p.179 run
the induction over these layers.

The source orders cells by analytic dimension. This file instead uses the usual
length of a permutation, its number of inversions, as a numerical encoding. It is
an internal construction for the dimension-layer argument. The source does not
use this encoding explicitly. This file proves no dimension formula. In
particular it does not prove that the dimension of a cell is an increasing
function of the inversion count. It also does not identify `upperBruhatLayerLE`
with Shalika's `ω_j`, nor `upperBruhatCellNeighborhood` with `Ω_w`. Those
comparisons, and every topological property, are separate later units.
As context only, `Langlands.Representation.Geometric.ClosedSubgroupOrbitOrdering`
and `Langlands.Representation.Geometric.CosetOrbitOrdering` give an existing
ordering of finitely many double cosets. Their hypotheses are Hausdorff, locally
compact, sigma-compact nonarchimedean groups with closed subgroups. This file
neither uses, duplicates nor presumes that ordering.

## Conventions and exact formulas

The permutation matrix `permutation n R w` sends `e_j` to `e_(w j)`, as in the
imported pair. The order on `Fin n` is the usual order, and `Fin.rev` is the
order-reversing involution `i ↦ n - 1 - i`.

- `permutationInversionCount n w` is the number of ordered pairs
  `(i, j) : Fin n × Fin n` with `i < j` and `w j < w i`.
- `g ∈ upperBruhatLayerLE n R k` exactly when some permutation `w` has
  `permutationInversionCount n w ≤ k` and `g ∈ upperBruhatCell n R w`.
- `g ∈ upperBruhatHigherCells n R w` exactly when some permutation `v` has
  `permutationInversionCount n w < permutationInversionCount n v` (strict) and
  `g ∈ upperBruhatCell n R v`.
- `upperBruhatCellNeighborhood n R w` is the union
  `upperBruhatCell n R w ∪ upperBruhatHigherCells n R w`.
- `upperBruhatTransposeIndex n w` is `Fin.revPerm * w⁻¹ * Fin.revPerm`. In
  `Equiv.Perm` the product is composition, `(σ * τ) i = σ (τ i)`. Hence the index
  sends `i` to `(w⁻¹ i.rev).rev`, and its inverse sends `i` to `(w i.rev).rev`.

The inversion count is not a new count. It reuses the published generic count
`Langlands.Combinatorics.relationInversions` from
`Langlands.Combinatorics.RelationInversions`, imported unchanged. For a decidable
relation `Rel` and a list `l`, `relationInversions Rel l` counts the pairs of
positions `i < j` of `l` whose entries satisfy `Rel (l[i]) (l[j])`. The adapter
is
`permutationInversionCount n w = relationInversions (fun a b : Fin n => b < a) (List.ofFn ⇑w)`.
The list `List.ofFn ⇑w` is `[w 0, w 1, ..., w (n - 1)]`, so its position `i` holds
`w i`. With the relation `b < a`, the pair of positions `i < j` is counted exactly
when `w j < w i`. This is the required ordered-pair count. The theorem
`permutationInversionCount_eq_card_permutationInversions` proves the agreement
with the `Finset` of inverted pairs, as described below.

At the pinned Mathlib commit there is no inversion count of this form.
`Equiv.Perm.finPairsLT n` is an auxiliary of `signAux`, which records only a sign
product. `CoxeterSystem.length` is abstract, and Mathlib provides no Coxeter
system on `Equiv.Perm (Fin n)` here.

## Declarations

| Lean name | Meaning |
| --- | --- |
| `permutationInversions n w` | The `Finset` of ordered pairs `(i, j)` with `i < j` and `w j < w i`. |
| `permutationInversionCount n w` | `relationInversions (fun a b : Fin n => b < a) (List.ofFn ⇑w)`, a natural number equal to the cardinality of `permutationInversions n w`. |
| `upperBruhatTransposeIndex n w` | The permutation `Fin.revPerm * w⁻¹ * Fin.revPerm`. |
| `upperBruhatLayerLE n R k` | The union of the actual cells `C_w` with `permutationInversionCount n w ≤ k`. |
| `upperBruhatHigherCells n R w` | The union of the actual cells `C_v` with `permutationInversionCount n w < permutationInversionCount n v`. |
| `upperBruhatCellNeighborhood n R w` | `C_w ∪ upperBruhatHigherCells n R w`. |

All sets are subsets of `Langlands.GeneralLinear n R`, which is Mathlib's group
of invertible matrices.

## Proved laws and their proofs

Adapter for the reused count. These two lemmas hold for every type `α` in an
arbitrary universe and every decidable relation `Rel` on it. The relation is
named `R` in the Lean section `Adapter`; it is unrelated to the ring `R` below.

- `relationPairCount_singleton_ofFn` states that
  `relationPairCount Rel [a] (List.ofFn f)` equals the sum over `j : Fin m` of
  `if Rel a (f j) then 1 else 0`. It unfolds `relationPairCount` and uses
  `Fin.sum_ofFn`.
- `relationInversions_ofFn_eq_card` states that
  `relationInversions Rel (List.ofFn f)` is the cardinality of the set of
  ordered pairs `(i, j) : Fin m × Fin m` with `i < j` and `Rel (f i) (f j)`. The
  proof is by induction on `m`. The case `m = 0` is the empty list and the empty
  set. For `m + 1`, `List.ofFn_succ` splits off the head `f 0`. The defining
  recursion `relationInversions_cons` then gives the pairs starting at the head
  plus the count for the tail `fun i => f i.succ`. The induction hypothesis
  handles the tail. The right side is rewritten as a double sum of indicators by
  `Finset.card_filter` and `Fintype.sum_prod_type`. Both sums are split at index
  `0` by `Fin.sum_univ_succ`. A pair with second index `0` contributes nothing.
  Pairs `(0, j.succ)` give the head term. Pairs `(i.succ, j.succ)` give the tail
  count, by `Fin.succ_lt_succ_iff`.

Inversion count.

- `permutationInversionCount_eq_relationInversions` is the adapter equation,
  by `rfl`.
- `mem_permutationInversions_iff` is the membership formula, by unfolding the
  filter.
- `permutationInversionCount_eq_card_permutationInversions` proves that the
  count equals the cardinality of `permutationInversions n w`. It is
  `relationInversions_ofFn_eq_card` for the relation `b < a` and `f = ⇑w`.
- `permutationInversionCount_eq_card` restates this with the filtered universe
  of `Fin n × Fin n` written out.
- `permutationInversionCount_eq_fintypeCard` gives the same count as the
  cardinality of the subtype of inverted pairs, by `Fintype.card_subtype`.
- `permutationInversionCount_one` shows that the identity has no inversions.
  Through the cardinality form, an inverted pair of the identity would need
  both `i < j` and `j < i`.

Transpose index.

- `upperBruhatTransposeIndex_apply` is the evaluation formula
  `upperBruhatTransposeIndex n w i = (w⁻¹ i.rev).rev`. Its proof rewrites twice
  with `Equiv.Perm.mul_apply` and then with `Fin.revPerm_apply`.
- `upperBruhatTransposeIndex_inv_apply` gives the inverse,
  `(upperBruhatTransposeIndex n w)⁻¹ i = (w i.rev).rev`. It follows from
  `Equiv.Perm.inv_eq_iff_eq`, the evaluation formula and `Fin.rev_rev`.
- `upperBruhatTransposeIndex_upperBruhatTransposeIndex` is the involution law
  `upperBruhatTransposeIndex n (upperBruhatTransposeIndex n w) = w`. It is
  proved pointwise from the two formulas above and `Fin.rev_rev`.
  `upperBruhatTransposeIndex_involutive` packages it as `Function.Involutive`.
- `upperBruhatTransposeIndex_one` shows that the index of the identity is the
  identity.
- `permutation_upperBruhatTransposeIndex` states
  `permutation n R (upperBruhatTransposeIndex n w) =
  weylLong n R * (permutation n R w)⁻¹ * weylLong n R` over every commutative
  ring. The proof uses only that `permutation n R` is a group homomorphism and
  that the imported `weylLong n R` is `permutation n R Fin.revPerm`. A
  permutation matrix's inverse is its transpose, which explains the name. That
  fact is not proved here, and this lemma says nothing about cells.

Cell sets.

- `mem_upperBruhatLayerLE_iff`, `mem_upperBruhatHigherCells_iff` and
  `mem_upperBruhatCellNeighborhood_iff` are the exact membership formulas,
  by `Iff.rfl`.
- `upperBruhatLayerLE_eq_iUnion` writes the layer as the indexed union
  `⋃ w, ⋃ (_ : permutationInversionCount n w ≤ k), upperBruhatCell n R w`.
- `upperBruhatLayerLE_mono` proves monotonicity in `k`, as `Monotone`, by
  `le_trans` on the witness. `upperBruhatLayerLE_subset` gives the same
  inclusion for `k ≤ l`.
- `upperBruhatCell_subset_upperBruhatLayerLE` includes a cell with at most `k`
  inversions in the `k`-th layer.
- `upperBruhatCell_subset_upperBruhatHigherCells` includes the cell `C_v` in
  the higher union of `w` when `v` has strictly more inversions.
- `upperBruhatCell_subset_upperBruhatCellNeighborhood` and
  `upperBruhatHigherCells_subset_upperBruhatCellNeighborhood` are the two
  inclusions into the neighborhood.

## Exclusions

These are transparent set and permutation constructions, not geometric
conclusions. No definition contains as a field or hypothesis any of the
following, and none of them is proved here:

- closure or boundary properties;
- closedness of layers or openness of the neighborhoods;
- disjointness or coverage of the cells, or a Bruhat decomposition;
- preservation of the inversion count by `upperBruhatTransposeIndex`;
- that transpose, `θ`, or any Weyl-twisted transpose maps `C_w` to
  `C_(upperBruhatTransposeIndex n w)`.

Individual cells are not assumed to be transpose-stable. There are no
distribution, orbital-integration, analytic-manifold or dimension assertions.
