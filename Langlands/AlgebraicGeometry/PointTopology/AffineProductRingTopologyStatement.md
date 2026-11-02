# Affine points over a product of value rings

Author: Worker 208.

This is a derived generalization of the affine homeomorphism assertion in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Theorem 3.6, formula (3.6.1), printed page 6, and the
product-topology argument in its proof on printed page 8. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`AffineProductRingTopologyStatement` is a proposition-valued definition in
namespace `Langlands.AlgebraicGeometry.PointTopology`. For a commutative
ring `C`, an arbitrary index type `ι`, a family of commutative `C`-algebras
`R i` with topologies, and an actual affine scheme `X` over `Spec C`, it
asserts that the existing map

`productPointMap C R X : RingPoint C X (∀ i, R i) → ∀ i, RingPoint C X (R i)`

is a homeomorphism. Each point is an actual morphism over `Spec C`.
The map restricts it along the spectrum of each coordinate projection
`Pi.evalAlgHom C R i`.

The value ring `∀ i, R i` has its usual product topology. Every actual
affine scheme point space has the published topology induced by
`affineSchemePointEquiv` from evaluation of algebra maps out of the actual
global-section algebra `AffineCoordinateRing C X`. The target has the
product of these point-space topologies. The statement changes none of
these constructions.

All the rings, the scheme, and the index type lie in one arbitrary universe
`u`, as required by the existing scheme-point interfaces. Empty and infinite
index types are included. The target assumes only `IsAffine X.left` and
the stated ring, algebra, and topology instances. It requires no finite
type or finite presentation, local-ring condition, separation condition on
the value topologies, continuity of ring operations, or topology on `C`.

The reason for the derived generality is that an algebra map into a product
is exactly a family of algebra maps, and evaluation on each coordinate of
the value product determines its topology. Transport through the canonical
affine scheme/algebra comparison gives the asserted actual point map.
Conrad's source assertion specializes this reasoning to finite-type
`O_{F,S}`-schemes and the product of the local value rings defining
`A_{F,S}`; his proof uses a finite coordinate presentation to exchange the
two product topologies. The present target states the corresponding
evaluation-topology assertion independently of that arithmetic
specialization.

This unit supplies a statement for a subsequent proof. Instantiating the
actual global-field local and adelic rings, comparing the base-changed
local point spaces in (3.6.1), and proving the nonaffine and change-of-`S`
topology assertions remain separate obligations.
