# Weighted positive-root sums on nested blocks

`Langlands.Exponents.PositiveRootBlockSumsStatement` is a closed proposition
definition. It bundles three finite-algebra consequences of the existing
`RelativeRegularComparison.IsPositiveRootParameter`. This file states those
consequences; it does not prove them.

For an ordered middle block shape `D`, its actual refinement `R`, and
`v : Fin (D.flatten R).length → ℝ`, the first two clauses assume precisely
`IsPositiveRootParameter D R v`. For each middle block `i`, the first clause
asserts

`∑ k, ((R i).size k : ℝ) * v (D.flattenBlockEquiv R ⟨i,k⟩) = 0`.

The fine determinant exponent is therefore multiplied by its actual fine
block size. The second clause expands it to the actual scalar-coordinate
vector

`x(a) = v (Geometric.blockIndex (D.flatten R) a)`.

It asserts `∑ a : Fin (D.size i), x (D.index i a) = 0` on every middle block.
The numbering and block membership use the Library's actual consecutive
coordinate maps.

The third clause fixes a coarse shape `B`, its refinement `Q`, a refinement
`R` of `D = B.flatten Q`, another refinement `S` of `B`, and the literal
ordered-shape equality `h : D.flatten R = B.flatten S`. For the same positive
root parameter `v`, transport gives `h ▸ v` on `B.flatten S`. Its expanded
scalar-coordinate vector has zero sum on every coarse block:

`∑ a : Fin (B.size i),
  (h ▸ v) (Geometric.blockIndex (B.flatten S) (B.index i a)) = 0`.

No extra compatibility between independently supplied maps is assumed: the
transport is equality transport between actual block shapes, and all other
maps come from the given refinements.

## Internal provenance

This is a source-free internal algebraic adapter for published definitions.
Within a middle block with fine sizes `d_k`, the supplied root expansion is

`v_k = ∑ j, c_j * (1_(k=j)/d_k - 1_(k=j+1)/d_k)`.

Each size is a positive natural number. Multiplying by `d_k` cancels its
reciprocal. For each adjacent root `j`, the two indicator sums over all fine
blocks each equal one, so their difference has sum zero. Finite distributivity
and exchange of sums yield the first clause. The hypothesis retains the
strict positivity of every `c_j`, although this cancellation uses only the
given expansion.

Reindex the coordinates of a middle block through `(R i).indexEquiv`.
`BlockShape.index_index_eq_flatten` identifies each resulting coordinate with
its actual flattened fine block, and `Geometric.blockIndex_index` recovers
that block. Its value repeats exactly `d_k` times. Summing those repeated
values gives the weighted sum in the first clause, hence the second clause.
Reindexing a coarse block through `(Q i).indexEquiv` similarly decomposes its
sum into middle-block sums. Equality transport along `h` preserves the
expanded vector, so the zero middle sums yield the third clause.

These are assertions over every natural rank, including zero. At zero rank
the positive-size condition forces every block index set to be empty, so
the blockwise conclusions are vacuous. A middle block with one fine block
has an empty adjacent-root index set; the supplied expansion sets its
parameter to zero. No separate exception or positive-rank premise is used.

## Scope

The coarse zero sums provide the zero-sum hypothesis used by the published
`Langlands.Exponents.closedConeStabilizerRigidity`. They provide no permuted
closed-cone condition, occurrence or persistence of a constituent, analytic
continuation, multiplicity comparison, irreducible head or classification.
There is no representation-theoretic assertion in this statement and no
attribution of a new theorem to Silberger.
