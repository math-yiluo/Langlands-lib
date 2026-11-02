# Affine product topology and canonical projection statements

Author: Worker 105.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1 and its proof, printed page 2.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`TensorProductTopologyProperty R A B S` asserts that the canonical restriction
map from the actual algebra-map points of `A ⊗[R] B` to pairs of actual points
of `A` and `B` is a homeomorphism. The point spaces carry their evaluation
topologies and the pair carries the product topology. The base and coordinate
rings are arbitrary commutative rings; only the value ring `S` is topological,
with continuous addition and multiplication. No finite generation,
Hausdorffness, locality or continuity of the base algebra maps is assumed.
The algebra-map statement allows the four rings to lie in independent
universes.

`SpecProductProjectionProperty`, in a common universe, identifies the previously
constructed `specProductPointPairEquiv` with the actual scheme pullback
projections: after forgetting the equations over the base, its first component
is composition with `pullback.fst` and its second is composition with
`pullback.snd`. This is an algebraic assertion with no topology assumptions.
It makes explicit that the comparison map is the geometric product-point map.

`SpecProductTopologyProperty` asserts that this comparison on actual scheme
points is a homeomorphism. Its domain has the affine tensor-coordinate topology
constructed in `AffineProducts`; its codomain has the product of the published
factor evaluation topologies. It has the same topological-ring assumption on
`S` as the algebra-map assertion.

`AffineProductProperties` combines the projection identification and the two
topological assertions in a common universe. It imposes the topological-ring
assumption separately on the two topological clauses. These are Prop-valued
statement targets, with proofs delivered separately.

The product topology conclusion is Conrad's Proposition 2.1. Its formulation
for arbitrary coordinate algebras is the intrinsic evaluation-topology
extension of the source's finite-type assertion: evaluation at a tensor is a
finite sum of products of factor evaluations. The projection assertion is a
derived host comparison to Mathlib's actual scheme pullback, which identifies
that tensor calculation with the source's scheme product. General fibre
products, the axiomatic uniqueness assertion and the rest of Proposition 2.1
remain separate obligations.
