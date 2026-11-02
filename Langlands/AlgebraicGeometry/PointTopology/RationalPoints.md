# Identity-test and evaluation-topologized rational points

This unit identifies actual scheme points tested by the identity map of
`Spec R` with the existing base-valued `RingPoint R X R`. It transports the
published affine evaluation topology across that canonical identification.
The maps in both directions preserve the underlying scheme morphism exactly.

## Source and provenance

This is a derived host adapter for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Proposition 2.1 and its proof,
printed pages 2–3. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The paper equips actual rational points of affine schemes with their evaluation
topology. The Library already constructs that topology on
`RingPoint R X R = (ringTest R R ⟶ X)`. Some consumers write the same points
as morphisms from `Over.mk (𝟙 (Spec (CommRingCat.of R)))` instead. This unit
proves the comparison between these two host conventions; it is not a new
source assertion about rational points or a new choice of their topology.

The coefficient ring `R : Type u` is an arbitrary commutative ring, and
`X : Over (Spec (CommRingCat.of R))` is arbitrary for the carrier comparison.
For the topology, `X.left` is affine and `R` has an arbitrary topology. No field,
local-ring, finiteness, separation or continuity hypothesis is imposed.

## Exact constructions and comparisons

All declarations lie in `Langlands.AlgebraicGeometry.PointTopology`.

- `ringTestSelfIso R` is the actual relative scheme isomorphism
  `ringTest R R ≅ Over.mk (𝟙 (Spec (CommRingCat.of R)))`. Its underlying
  scheme map in either direction is the identity. It uses the identity
  algebra map of the base ring and functoriality of `Spec`.
- `RationalPoint R X` abbreviates the actual morphism type
  `Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X`.
- `rationalPointEquiv R X` is an equivalence from `RationalPoint R X` to
  `RingPoint R X R`, by precomposition with the identity-test isomorphism.
  `rationalPointEquiv_left` and `rationalPointEquiv_symm_left` prove that
  both directions preserve the underlying scheme morphism.
  `rationalPointEquiv_natural` proves that this identification commutes with
  actual postcomposition by every relative scheme morphism `X ⟶ Y`.
- `rationalPointTopology R X` is exactly the topology induced by
  `rationalPointEquiv R X` from the existing affine evaluation topology on
  `RingPoint R X R`. It is a named topology and installs no global instance
  on the rational-point carrier.
- `rationalPointHomeomorph R X` is the resulting homeomorphism from the
  identity-test point carrier, equipped explicitly with
  `rationalPointTopology R X`, to the existing evaluation-topologized
  `RingPoint R X R`. `rationalPointHomeomorph_left` proves that the forward
  homeomorphism preserves the underlying scheme morphism.

The topology and homeomorphism are therefore actual transports of the
published construction. A consumer with another explicitly bound topology
can require equality to `rationalPointTopology R X`; this does not leave its
canonical topology as an uninstantiated assumption. Local compactness,
continuity of group operations, and compact-open subgroup properties are
separate results and are not claimed by this carrier adapter.
