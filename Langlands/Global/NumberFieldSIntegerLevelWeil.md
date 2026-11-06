# Actual number-field adelic-level Weil points

This derived construction instantiates Conrad, *Weil and Grothendieck
approaches to adelic points* (2011), Example 4.2, printed pages 9–10,
especially the finite-level comparison on page 10. It uses actual number
fields K and L with their original embedding, every finite lower exceptional
set S, the actual lower S-integer ring, and the actual upper S-integer ring
at the full exceptional preimage. All archimedean places are included by the
existing full number-field adelic-level construction.

`Above` associates to each original lower level coordinate every original
upper place above it. Infinite coordinates use `InfinitePlacesAbove`;
finite coordinates, both inside and outside S, use `FinitePlacesAbove`.
`upperFactor` is the original upper completion in the infinite and
finite-in-S cases, and the original upper completed integer ring outside S.
Its scoped ring, topology, local-ring and open-unit instances come from
these original rings. Every upper-place family is finite.

The upper global coefficient action is its original inclusion in each
completed field, and the proved `NumberFieldSIntegerLocalTensor.upperMap`
in each completed integer ring. The lower-factor action is the original
completion embedding, restricted to integers in the integer case. The
finite-module and projective-module instances reuse the existing local
extension results; in the field cases projectivity follows from freeness
over the lower field. For field factors their original topology is the
module topology by finite dimensionality over the nontrivially normed lower
completion. Integer factors reuse the proved compact finite-module topology.
Both real and complex infinite places are included.

`tensorEquiv` reuses the proved original S-integer completed-field tensor
comparisons at finite and infinite places and the completed-integer tensor
comparison outside S. In each field case, algebra extensionality verifies
that the coefficient action from the literal adelic-level projection equals
the native subalgebra action through K. The private `tensorData` transports
the equivalence and its right-coefficient formula together along this proved
equality. The integer case uses the original tensor comparison directly.
`tensorEquiv_one_tmul` therefore retains exactly the original upper
coefficient map in every factor. These are proved comparisons, not inputs
assumed from an abstract place system.

Let Y be an actual upper model that is locally of finite type, quasi-compact
(`CompactSpace Y.left`) and quasi-separated, with a specified relative
immersion into finite-dimensional projective space. This immersion gives
separatedness and finite affine neighborhoods. `levelPointHomeomorph`
constructs a homeomorphism from points of the actual integral Weil model
over the actual lower adelic level to all original upper factor points,
indexed by the lower coordinate and an upper place above it. Its source
uses the existing `numberFieldLevelModelPointTopology`; each upper point
space uses `schemePointTopology`, and the target has their product topology.

The proof first uses the original `numberFieldLevelFactorAlgEquiv` and the
existing equality of the level topology with the induced product-point
topology. It then applies the proved `productTensorWeilPointHomeomorph`
with the actual local tensors, scalar maps and module topologies above.
`levelPointHomeomorph_component` verifies that every output component is
exactly `completedTensorWeilRestrictionPointMap` applied after the literal
original `numberFieldLevelFactorAlgHom` projection of the level point.
The projection identity follows from composition of the original test
spectrum maps. Thus this construction preserves the original local counits.

No quasi-compactness or finite-type assertion about the Weil scheme is
assumed. The original upper model supplies the product-point bijection.
Regrouping the paired index into the actual upper level, compatibility when
levels enlarge, and the final full adelic Weil homeomorphism are separate
remaining host obligations.
