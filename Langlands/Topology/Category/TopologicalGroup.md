# The category of topological groups

`Langlands.Topology.TopologicalGroup` bundles an actual group, its topology,
and the continuity of multiplication and inversion. Its morphisms are
`ContinuousMonoidHom`; thus they are continuous homomorphisms of the given
groups, without a separation, local compactness, or discreteness assumption.
Composition is ordinary composition of these homomorphisms.
The category is concrete, with morphisms acting by their original functions;
`TopologicalGroup.hom_ext` proves equality from equality at every element.

`TopologicalGroup.of` bundles an existing topological group without changing
its carrier or structures. `TopologicalGroup.forget` sends it to the original
topological space and sends each homomorphism to its underlying continuous map.
This functor is faithful: equality of the continuous maps gives pointwise
equality of the homomorphisms.

This is internal categorical infrastructure for the category of operator
groups in Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(1996 unfinished manuscript), section 1.1, printed/PDF page 3. The original
names the category of topological groups as the base of the category of
analytic spaces with operators; the elementary bundling and functor here are
an implementation of that base, not an analytic-space construction.

The carrier has universe `v`, and the bundled category has universe `v + 1`.
