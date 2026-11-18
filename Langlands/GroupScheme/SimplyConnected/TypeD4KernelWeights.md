# Actual vertices and weights of the centrally marked D4 kernel

Author: Worker 177.

This unit is an internal specialization of the actual anisotropic-kernel
comparison and actual character-restriction constructions. It works over
every field and characteristic. Its input is actual `TitsIndexData d`
with a complete numbering `q` by `CartanMatrix.D 4` whose unique
distinguished vertex is the central vertex 1. No local-field or rank
hypothesis is used to obtain or replace that marking.

`zeroVertices_iff_D4_leaf` takes the complement of the exact marking
condition. It identifies the zero vertices with the three numbered leaves
0, 2 and 3. `d4ZeroLeafNumbering` enumerates those zero vertices in that
order, using the standard equivalence that deletes vertex 1 from `Fin 4`.

For an actual `p : d.AnisotropicKernelIndex`,
`p.d4LeafNumbering q hq` composes that enumeration with the published
equivalence from the kernel's actual simple vertices to the ambient zero
vertices. The ambient-numbering theorem identifies each numbered kernel
vertex with the corresponding actual ambient leaf.

`cartan_D4_central_mark` checks every ordered Cartan entry. The actual kernel
matrix has diagonal entries 2 and off-diagonal entries zero. The proof
transports the full Cartan comparison and checks all nine entries in the
deleted D4 matrix. `cartanConnected_iff_eq_D4_central_mark` then proves that
each actual connected Cartan component consists of one vertex: every
generating off-diagonal edge is impossible, and the equivalence-relation
closure preserves equality. Thus this describes three isolated A1
components of the actual kernel diagram.

`d4LeafNumbering_star` transports the published full-star comparison through
the numbering. It preserves the action of each element of the original
absolute Galois group, including permutations between the three components.

For simply connected ambient `G`, the actual anisotropic kernel is simply
connected by the published centralizer-derived theorem.
`weightRestriction_D4_leaf` uses that fact to supply both full integral
coroot-span conditions and specializes the published fundamental-weight
restriction theorem at each actual leaf. Restriction along the actual
kernel torus sends the ambient fundamental weight at 0, 2 or 3 to the
corresponding actual integral kernel fundamental weight. The central
fundamental weight restricts to zero by the published distinguished-weight
restriction theorem.

All restrictions are morphisms of actual integral character lattices after
base change to the original separable closure. This unit constructs no
individual component group over a vertex field, norm-one presentation of
such a component, actual Tits obstruction, Brauer transfer, local invariant
or local D4 exclusion. Its provenance is the explicitly described
specialization and finite matrix computation; no external theorem is
claimed.
