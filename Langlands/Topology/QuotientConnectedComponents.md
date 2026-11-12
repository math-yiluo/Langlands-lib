# Connected components of a quotient

Author: Worker 107.

This is an internal topological construction for the atlas-incidence proof of Conrad's
Lemma 5.1. Let `f : A → B` be a quotient map, and suppose the actual component space
`ConnectedComponents A` is discrete. This includes a Noetherian source, for which
connected components are open.

`componentFibreRelation f c d` means that a fibre of `f` meets both source components:
there are points `x` in `c` and `y` in `d` with `f x = f y`.
`quotientConnectedComponentsEquiv` constructs an equivalence between
`Quot (componentFibreRelation f)` and `ConnectedComponents B`. A `Quot` identifies the
equivalence closure of its generating relation, so it accounts for arbitrary finite
chains of fibre identifications. No finiteness of the source component set is required.

The forward map sends a source component to its image component in `B` and respects
fibre identifications by continuity. For the inverse, choose a point in each fibre of
`f` and take the quotient class of its source component. Its composite with `f` is the
canonical component-class map, which is continuous because the source component space
is discrete. The quotient-map property of `f` therefore makes the inverse map continuous
into the discrete class set. It factors through `ConnectedComponents B`; evaluation on
point representatives proves both inverse identities.

`componentCount_eq_of_fibreRelationEquiv` composes these equivalences for two quotient
maps with an equivalence of source component sets preserving fibre incidence, then
applies cardinality invariance. The counts are in `ℕ∞`, and the result also covers
infinite component sets. This isolates the topological step; it does not spread scheme
components or prove constructibility of algebraic families.
