# Actual graphs of group-scheme homomorphisms

Author: Worker 1656.

This module constructs the graph of an actual group-scheme homomorphism
`f : H ⟶ G` over any scheme `S` in an arbitrary universe `u`. It is an
internal categorical construction from products and represented subgroup
functors. It supplies a graph correspondence needed in the proof of smooth
Hom representability; it asserts no representability of a moduli functor.

`graphHom f` is the product lift of the identity of `H` and `f`. Its first
projection is the identity and its second projection is `f`. The first
projection supplies a retraction, proving that the underlying map over
`S` is a monomorphism. If `G → S` is separated, the first projection
`H ×_S G → H` is separated. Composing the graph with this projection gives
the identity, so the separated cancellation theorem for closed immersions
shows that the graph is closed. Affine targets satisfy the required
separatedness hypothesis.

`graph f` is the pointwise range subgroup functor of `graphHom f` on all
test schemes over `S`. The graph homomorphism represents this functor.
The theorem `mem_graph_iff` identifies membership with the equality of
the second projection and the first projection followed by `f`, as actual
maps over `S`. Applying this criterion to the graph homomorphism itself
proves `graph_injective`.

`IsGraph F` asks for an actual representative `j : K ⟶ H ×_S G` of the
subgroup functor `F`, such that `j` followed by the first projection is an
isomorphism of group schemes. Given such a representative,
`homOfGraphRepresentative j` composes the inverse of that projection
with `j` and the second projection. Product extensionality identifies
its graph with `j` precomposed by that inverse. Precomposition with an
isomorphism preserves the range subgroup functor, so recovery gives
exactly `F` on every test scheme. Graph injectivity makes recovery unique.
`graphEquiv` packages the resulting equivalence between actual
homomorphisms and these graph subgroup functors.

No hypotheses of smoothness, finite type, reducedness, connectedness or
Noetherianness enter the correspondence. The only geometric hypothesis
in the module is separatedness in the closed-graph theorem. The module
does not construct a scheme parametrizing these subgroups, an open
isomorphism locus, or a universal relative Hom family. Those are separate
obligations in the assigned representability theorem.
