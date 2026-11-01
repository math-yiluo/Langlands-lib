# Actual bundle extension from surjectivity of two-axis classes

This module gives an internal conditional reduction of the published
`Langlands.AbelianScheme.ValuationRingTwoAxisExtensionStatement` to
surjectivity of the published presheaf of compatible two-axis-rigidified
line-bundle classes. It constructs an actual extending line bundle and an
actual module-sheaf restriction isomorphism. The surjectivity assumption
remains an explicit hypothesis: the module does not prove the
unconditional valuation-ring extension statement.

All schemes and rings range over an arbitrary universe `u`. The geometric
constructions first apply to every abelian scheme `A` over every scheme
`S`, without assumptions on a valuation ring or a fraction field.

## Comparing the actual product maps

For a test-scheme map `b : T ⟶ S`, `TwoAxisFamily.toBase b` is the
morphism from `Over.mk b` to the identity test scheme `Over.mk (𝟙 S)`.
`TwoAxisFamily.productToBase A T` is the canonical projection from the
self-product of the actual base change of `A` at `T` to the original
self-product. It is the published `mumfordProductBaseChangeMap`.

`productMap_toBase` states that every family map commutes with these
projections. The proof uses extensionality for the original product:
on each factor it rewrites the two pullback projections and then uses
`productMap_fst` or `productMap_snd`, followed by `carrierMap_fst`.

The definition `productIdentityIso A` identifies the actual self-product
at the identity test scheme with the original self-product. It composes
the published `mumfordProductBaseChangeIso A (𝟙 S)` with the isomorphism
whose hom is the first projection of the pullback along `𝟙 S`.
`productIdentityIso_hom` identifies its hom with `productToBase`.
Consequently `productToBase_comp_identity_inv` proves the equality

`mumfordProductBaseChangeMap A b ≫ (productIdentityIso A).inv =
  TwoAxisFamily.productMap A (TwoAxisFamily.toBase b)`.

The proof cancels the isomorphism's hom and uses `productMap_toBase`.
This equality retains the actual canonical map used in the published
extension target.

## Extracting a representative and an extending bundle

For every test-scheme morphism `h : T ⟶ U`,
`TwoAxisRigidifiedLineBundle.exists_pullback_iso_of_classesPullback_surjective`
assumes surjectivity of `classesPullback A h`. Given an actual compatible
rigidified line bundle `L` at `T`, it produces an actual such bundle `M`
at `U` and a nonempty type of compatible isomorphisms
`(relativePullback A h).obj M ≅ L`. The proof applies surjectivity to the
class of `L`, eliminates the chosen preimage class into the existential
proposition, and uses `Quotient.exact` to recover a compatible isomorphism
of representatives. This is stronger data than equality after forgetting
the two rigidifications.

`actualBundleExtension_of_classesPullback_surjective` specializes this
argument to `toBase b`. Its inputs are a line bundle `D` on the actual
base-changed self-product and nonempty types of trivializations of its
restrictions to both unit axes, in the same orientation as the published
extension target. The published `nonempty_twoAxisRigidification` supplies
compatible rigidifications of `D`. Class surjectivity then gives a
representative `M` over the identity test scheme and its compatible
restriction isomorphism.

Let `N` be the underlying line bundle of `M`, and let
`J = productIdentityIso A`. The extending line bundle is explicitly
`E = (LineBundle.pullback J.inv).obj N` on the original self-product.
Its required underlying module-sheaf isomorphism is the composite of:

1. the module pullback comparison for the canonical product map and
   `J.inv`;
2. the pullback comparison induced by
   `productToBase_comp_identity_inv`;
3. the underlying module-sheaf isomorphism of the compatible restriction
   isomorphism of `M` with the chosen rigidification of `D`.

Thus the conclusion concerns the actual pullback along
`mumfordProductBaseChangeMap A b`, rather than just a quotient class.
The conclusion does not require the given axis trivializations to extend.

## The valuation-ring specialization and its scope

`Langlands.AbelianScheme.valuationRingTwoAxisExtension_of_classesPullback_surjective`
assumes that, for every valuation domain `R`, every chosen fraction field
`K` with the specified `Algebra R K` and `IsFractionRing R K` structures,
and every abelian scheme over `Spec R`, restriction of compatible classes
along the map from `Spec K` to the identity test scheme is surjective.
It then proves the exact published extension proposition by the preceding
bundle construction. It preserves arbitrary-rank valuation rings,
including fields, and the specified algebra map and product pullback.

This final theorem has an outer surjectivity hypothesis. No theorem in
this module removes it, constructs a representing scheme, proves a
valuative existence assertion, or proves Raynaud XI 1.5. The module is an
intermediate definition contribution, not an exact-target proof
submission for the host task.

## Provenance

The construction is internal. It uses the published
`TwoAxisRigidifiedClassPresheaf`, its actual compatible pullback functor
and isomorphism-class quotient, the normalization theorem in
`TwoAxisRigidification`, the comparisons in `SelfProductBaseChange`, and
the existing module and line-bundle pullback comparison isomorphisms.
Its proofs are categorical projection calculations, quotient elimination
and composition of the resulting actual isomorphisms. No additional
literature theorem is asserted or assumed implicitly.
