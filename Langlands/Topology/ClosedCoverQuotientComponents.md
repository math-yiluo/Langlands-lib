# Components of a quotient from a finite connected closed cover

This internal topological construction builds on
`Langlands.Topology.QuotientConnectedComponents`. It permits a finite closed
connected cover of the source in place of its actual connected-component
decomposition. This is useful when closed irreducible pieces of a generic
scheme fibre have been spread to nearby fibres.

For a family `s` of subsets of a space `A`, `coverSumMap s` maps the topological
disjoint union of the subspaces `s i` to `A` by forgetting the label.
If the family is finite, closed, and covers `A`, this map is a quotient map:
it is continuous and surjective, and images of closed sets are finite unions
of closed images under the closed subspace inclusions.

If every `s i` is connected and nonempty, `coverSumComponentsEquiv` identifies
the connected components of this disjoint union with its labels. The forward
map is the continuous summand-label map, factored through connected components
with discrete topology on the labels. The inverse selects one point of each
nonempty piece. Connectedness makes this choice independent after passage to
components. The forward map is continuous and injective into a discrete space,
so the component space of the disjoint union is discrete. No finiteness is
needed for these two assertions.

Given a quotient map `f : A → B`,
`coverFibreRelation f s i j` means that some point of `s i` and some point of
`s j` have equal images under `f`. The composite of `coverSumMap s` and `f`
is a quotient map. Under the label equivalence just constructed, its
component fibre relation is precisely `coverFibreRelation f s`.
`closedCoverQuotientComponentsEquiv` therefore identifies the quotient of the
finite label set by the generated image-incidence relation with the actual
connected components of `B`. `componentCount_eq_closedCoverIncidence` takes
`ENat.card` of this equivalence.

The result includes the empty-space case with an empty label set. Each
label that is present must index a nonempty connected piece. It makes no
claim that the images of the pieces in `B` are closed, and needs no such
assumption: closedness is required in `A`. Geometric spreading and
constructibility are separate inputs.
