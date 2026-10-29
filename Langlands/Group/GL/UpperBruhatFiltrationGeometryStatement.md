# Closed inversion layers and open neighborhoods of actual upper Bruhat cells

Author: Worker 914.

`Langlands.GeneralLinear.UpperBruhatFiltrationGeometryStatement.{u}` is a closed,
transparent `Prop`-valued definition in
`Langlands.Group.GL.UpperBruhatFiltrationGeometryStatement`. This module states
the proposition only; it provides no proof of it. The proof is a separate
obligation.

## Exact proposition

The proposition is

```text
∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [T2Space K] (n : ℕ),
  (∀ k : ℕ, IsClosed (upperBruhatLayerLE n K k)) ∧
    (∀ w : Equiv.Perm (Fin n), IsOpen (upperBruhatHigherCells n K w)) ∧
    (∀ w : Equiv.Perm (Fin n), IsOpen (upperBruhatCellNeighborhood n K w)) ∧
    ∀ w : Equiv.Perm (Fin n),
      IsClosed {g : upperBruhatCellNeighborhood n K w | g.val ∈ upperBruhatCell n K w}
```

It ranges over every field `K` in the universe `u`, every topology on `K` for
which `K` is a topological division ring (continuous addition, negation,
multiplication and inversion away from zero), and that topology is Hausdorff. It
ranges over every natural rank `n`, including `n = 0`. Inside the four conjuncts,
every natural number `k` and every permutation `w` of `Fin n` is quantified
separately. All these quantifiers are inside the proposition. There is no
positivity, nontriviality, characteristic, valuation, local compactness, sigma
compactness or countability hypothesis.

For each such `K` and `n` the proposition asserts all four of the following.

1. For every `k : ℕ`, the layer `upperBruhatLayerLE n K k` is closed in
   `Langlands.GeneralLinear n K`.
2. For every permutation `w`, the union `upperBruhatHigherCells n K w` is open in
   `Langlands.GeneralLinear n K`.
3. For every permutation `w`, the neighborhood `upperBruhatCellNeighborhood n K w`
   is open in `Langlands.GeneralLinear n K`.
4. For every permutation `w`, the set of points `g` of the subtype
   `upperBruhatCellNeighborhood n K w` whose underlying matrix `g.val` lies in
   `upperBruhatCell n K w` is closed in that subtype. In other words, the cell is
   relatively closed in its neighborhood.

## Topologies

The ambient group `Langlands.GeneralLinear n K` is Mathlib's
`Matrix.GeneralLinearGroup (Fin n) K`, the units of the matrix ring. It carries
the existing instance `Units.instTopologicalSpaceUnits`. That topology is induced
by `g ↦ (g, op g⁻¹)` into the product of the matrix space with its opposite. The
matrix space carries the entrywise product topology `Pi.topologicalSpace`.
Conclusions 1–3 use this ambient topology.

In conclusion 4 the set `upperBruhatCellNeighborhood n K w` is coerced to a type,
and that type carries Mathlib's subspace topology `instTopologicalSpaceSubtype`,
induced from the ambient group by `Subtype.val`. The closed set is a subset of that
subtype, not of the ambient group. A private development check confirmed by `rfl`
that these instances are the ones elaborated. No other topology, quotient or
abstract model of the cells enters the statement.

## The sets

All sets are imported unchanged from `Langlands.Group.GL.UpperBruhatFiltration`
and `Langlands.Group.GL.UpperBruhatCells`.

- `upperBruhatCell n K w` is the actual double coset
  `{g | ∃ b₁ ∈ upperTriangularSubgroup n K, ∃ b₂ ∈ upperTriangularSubgroup n K,
  g = b₁ * permutation n K w * b₂}`. Here `upperTriangularSubgroup n K` consists of
  the invertible matrices whose entries `(i,j)` with `j < i` vanish. The matrix
  `permutation n K w` has entry `(i,j)` equal to `if w j = i then 1 else 0`. So it
  sends `e_j` to `e_(w j)`.
- `permutationInversionCount n w` is the number of ordered pairs `(i, j)` with
  `i < j` and `w j < w i`. It is the published specialization of
  `Langlands.Combinatorics.relationInversions` to the relation `b < a` on
  `List.ofFn ⇑w`.
- `g ∈ upperBruhatLayerLE n K k` exactly when some permutation `v` has
  `permutationInversionCount n v ≤ k` and `g ∈ upperBruhatCell n K v`.
- `g ∈ upperBruhatHigherCells n K w` exactly when some permutation `v` has
  `permutationInversionCount n w < permutationInversionCount n v` (strictly) and
  `g ∈ upperBruhatCell n K v`.
- `upperBruhatCellNeighborhood n K w` is
  `upperBruhatCell n K w ∪ upperBruhatHigherCells n K w`.

So the neighborhood is this exact union of actual cells, not an unspecified open
set. The statement does not assert that an individual cell is open in the ambient
group. It neither reverses `w` nor changes the subgroup or its topology.

## Source correspondence

The registered original is `shalika-1974-multiplicity-one`, J. A. Shalika,
*The multiplicity one theorem for GLn*, Ann. of Math. (2) 100 (1974), 171–193.
The retained file is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Printed pp.174, 175, 178 and 179 are one-based PDF pages 5, 6, 9 and 10. All four
were read; pp.175, 178 and 179 were also checked visually on rendered page
images. On 2026-10-28 no source-specific errata was found, either in the project
literature index entry for this source or in the Library's public notes.

On printed p.174, `H` is the diagonal subgroup and `U` the upper triangular
unipotent subgroup, so `HU` is the upper triangular subgroup. The double cosets
are `G_w = HUwU`, for `w` in a fixed system of representatives of `W = N(H)/H`.
The imported `upperBruhatCell n K w` is this actual double coset for the published
permutation matrix. Two monomial representatives of the same Weyl element differ
by a diagonal factor in `HU`. The proposition quantifies over all permutations, so
the direction of the permutation convention does not affect the correspondence.

Lemma 1.7 on printed p.175 assumes that `k` is a local field. It is followed by a
Corollary: for `w ∈ W`, let `Ω_w` be the union of `G_w` with the double cosets of
strictly larger dimension; then (1) `Ω_w` is open in `G`, and (2) `G_w` is a
submanifold of `Ω_w`. On printed p.178, `r₀ = -1 < r₁ < ... < r_N` are the
dimensions of the double cosets, including the empty set. For `1 ≤ j ≤ N`, `ω_j`
is the union of the double cosets of dimension `≤ r_j`. On printed p.179,
Lemma 1.16 uses that `Ω_w \ G_w` consists of the double cosets of dimension
greater than `r_j = dim G_w`. Its proof uses that `Ω_w` is open in `G`.
Proposition 1.17 treats a distribution on `Ω_w` with support in `G_w`. Its proof
applies the remark after Lemma 1.15 on p.178. That remark is made for a closed
submanifold `M₀` of a manifold `M`, here with `M = Ω_w` and `M₀ = G_w`.
The proof of Theorem 1.6 then inducts downward over the layers `ω_j`.

The four conclusions relate to the source as follows.

- Conclusion 3 is the count-based analogue of Corollary (1), the openness of
  `Ω_w` in `G`.
- Conclusion 4 is the analogue of only the closedness part of Corollary (2), in
  the form used through Lemma 1.15. No submanifold structure is asserted.
- Conclusion 1 is the analogue of the layers `ω_j` being closed. The source does
  not state this closedness separately.
- Conclusion 2 is the analogue of the openness of `Ω_w \ G_w`, the union of the
  double cosets of strictly larger dimension. The source does not state this
  separately either.

## Internal derived formulation

This package is an internal derived formulation chosen by the project. It is not a
verbatim source theorem, and it claims no source statement under these hypotheses.
It departs from the source in two ways.

First, the source orders double cosets by analytic dimension. The statement
instead uses the numerical inversion count `permutationInversionCount n w`, with
closed layers bounded by `≤ k` and strictly higher unions. As motivation only:
the proof of Lemma 1.7 parametrizes `G_w` by `HU × U_w⁻` (the line after the proof
prints the identification as `U × H × H_w⁻`). In the published convention
`permutationUnipotentMinus`, the possibly nonzero off-diagonal entries of `U_w⁻`
are the positions `(i, j)` with `i < j` and `w j < w i`. Their number is
`permutationInversionCount n w`. This suggests that over a local field the
dimension of `G_w` is an increasing function of the count. Neither this module
nor the Library proves any dimension formula. The statement contains no
dimension, and it does not identify `upperBruhatLayerLE` with `ω_j` or
`upperBruhatCellNeighborhood` with `Ω_w`.

Second, Shalika treats local fields only. The quantification over arbitrary
Hausdorff topological fields is an internal generalization. A local field whose
topology carries these instances is a special case; for example, Mathlib supplies
them for the normed fields `ℝ`, `ℂ` and `ℚ_[p]`. The generalization is suggested
by finite rank conditions. The cells are characterized by the ranks of the
lower-left submatrices (rows at least `i`, columns at most `j`). Upper bounds on
such ranks are vanishing conditions on finitely many minors. These are closed
conditions in the inherited topology, because `{0}` is closed in a Hausdorff
field. This indicates an intended proof route only. The module proves neither the
rank characterization, nor the Bruhat-order closure relations, nor any of the
four conclusions. The later proof may use this route or any other genuine
argument.

## Exclusions

The statement has no premise assuming any of the following: a boundary or
closure theorem, local closedness of the cells, a coordinate homeomorphism, a
finite-orbit ordering, a geometric certificate, local compactness, sigma
compactness or countability. All four conclusions are closed goals under the
stated field hypotheses alone.

It also asserts none of the following:

- that an individual cell `upperBruhatCell n K w` is open in the ambient group;
- disjointness or coverage of the cells, or a Bruhat decomposition (full Bruhat
  coverage is already available as `fieldUpperBruhatFactorizationTheorem` in
  `Langlands.Group.GL.UpperBruhatProof`, and the later proof may reuse it);
- local closedness of each cell, which is the separate statement
  `UpperBruhatLocalClosednessStatement`;
- Lemma 1.7's submanifold, analytic or dimension claims;
- injectivity or homeomorphism of `upperBruhatCellMap` or `upperBruhatTorusMap`;
- stability of an individual cell under transpose, `θ` or any Weyl-twisted
  transpose, or preservation of the count by `upperBruhatTransposeIndex`.

## Status

The proposition is stated and unproved. It is a common geometry prerequisite for
the Shalika distribution and Whittaker multiplicity-one developments. It is not a
proof of either parent theorem.
