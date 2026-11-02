# Proof that affine point topology commutes with products of value rings

Author: Worker 208. Checked and submitted by Worker 1103.

The theorem `affineProductRingTopology` proves exactly
`Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyStatement`
at its arbitrary universe `u`. The imported target records the derived
evaluation-topology generalization of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Theorem 3.6: the affine
assertion following (3.6.1) on printed page 6, with its product-topology
proof on printed page 8. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Conrad's proof embeds a finite-type affine scheme into affine space through
a finite presentation and compares two product topologies on `A^n`. The
Lean proof takes a different route. It works directly with the published
evaluation topology on algebra-map points, so it needs no presentation of
the coordinate algebra.

The proof first verifies that `affineRingPointEquiv` sends change of the
value algebra along `f : S →ₐ[C] T` to postcomposition by `f`. On underlying
ring homomorphisms this is precisely the fully faithful spectrum functor's
identity `Spec.preimage_comp`, followed by `Spec.preimage_map`. Passing
through the canonical isomorphism of an affine scheme with the spectrum of
its actual global-section algebra preserves this naturality, by
associativity of actual morphisms over `Spec C`. Both lemmas are private
proof helpers.

The private algebra-point homeomorphism sends an algebra map into the
product to the family of its compositions with the coordinate projections
`Pi.evalAlgHom C R i`. Its inverse is `AlgHom.pi` applied to the family of
component maps. Both inverse identities hold by evaluating on each algebra
element and each factor. The forward map is continuous into the product of
point spaces because each component is `AlgPoint.mapCoefficients` along a
coordinate projection, which is continuous for the product topology. For
the inverse map, the universal property `AlgPoint.continuous_iff` reduces
continuity to evaluation at each algebra element. Continuity into the value
product then reduces to each factor, where the map is a coordinate
projection followed by a continuous evaluation. No ring-operation
continuity or finite generation enters this argument.

For the actual scheme points, compose three homeomorphisms: the published
`affineSchemePointHomeomorph` into algebra-map points, the constructed
product homeomorphism, and the product of the inverse affine
homeomorphisms. The naturality already proved identifies the resulting
function with the existing `productPointMap`, component by component.
`productPointMap_isHomeomorph` follows from this identification, and the
final theorem proves the exact named target.

The proof retains empty and infinite index types, arbitrary commutative
value algebras with arbitrary topologies, and arbitrary affine schemes
over `Spec C`. It uses only `IsAffine X.left` and the stated ring, algebra
and topology instances. It supplies the evaluation-topology comparison.
The actual local and adelic ring specialization, its base-change
identifications, and the nonaffine topology results remain the separate
obligations recorded in the target's Markdown.
