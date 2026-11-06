# Etale local identity-component transporters from field-valued points

This internal adapter constructs an etale local transporter from a transporter
over an arbitrary field above a base point. The field may be the algebraic
closure of the residue field. A rational residue-field transporter, a
finite-separable realization, and an etale local section are not premises of the
construction. The resulting transporter lies in the actual relative identity
component throughout the chosen neighbourhood. The construction chooses a new
point; it asserts no recovery of the supplied field-valued point.

The base is `Spec R` for any commutative ring in an arbitrary universe `u`. The
ambient actual group scheme `G` is affine and smooth over this base. Its fibres
may be disconnected, and the base need not be reduced or Noetherian. The source
in `etaleIdentityTransporter` is the actual diagonalizable group `D_R(M)` for an
arbitrary additive commutative group `M` in the same universe. The two maps to
`G` are actual group homomorphisms; neither is required to be an immersion.

Fix `s : Spec R`, an arbitrary field `k : Type u`, a morphism
`b : Spec k → Spec R` whose unique point maps to `s`, and an actual section `g₀`
of the actual group pulled back along `b`. The input transporter condition is
`IsTransporter` for the two actual pulled-back maps. It quantifies every scheme
refinement and every source-group point, not just field-valued points. The other
input condition says that the range of `g₀` lies in the connected component of
the actual identity point of that pulled-back group. These are conditions on the
supplied geometric or other field transporter, rather than extra assumptions on
the final openness theorem.

`EtaleIdentityTransporterData` is defined for two maps from any actual source
group. It records a commutative ring `neighbourhoodRing`, an etale morphism
`projection : Spec neighbourhoodRing → Spec R` whose image contains `s`, an
actual over-morphism `pointMap` into `G`, its all-test transporter equation, and
`InRelativeIdentityComponent G pointMap`. Thus the chosen neighbourhood is
explicitly affine. The last condition has the published all-test meaning: in
every residue fibre of the original base, the pulled-back image lies in the
actual fibre identity component. Equivalently, the whole image of `pointMap`
lies in `RelativeIdentityComponent.underlyingSet G`.

`etaleIdentityTransporterOfSourceIso` gives the same result for a source supplied
with an actual group-scheme isomorphism from a diagonalizable group. It
precomposes both maps with the isomorphism and reflects the resulting transporter
equation by precomposing with its inverse.
`etaleIdentityTransporterOfSplitTorus` specializes this to the actual standard
split torus indexed by any finite type with specified `Fintype` and
`DecidableEq` instances. It uses `Diagonalizable.splitIso` and keeps the supplied
field point and its hypotheses unchanged.

The data also construct `baseChangedSection`, an actual section of the group
pulled back to the chosen etale neighbourhood.
`baseChangedSection_isTransporter` proves the all-test transporter equation for
the two actual pulled-back homomorphisms.
`baseChangedSection_inIdentity` proves relative identity-component membership in
this new family. `baseChangedSection_recovers` identifies projection of this
section into the original group with the selected `pointMap`. This recovery
concerns the newly constructed section, not the original field point `g₀`.

The implemented proof first uses the multiplicative pullback-point adjunction to
view `g₀` as an actual point of the original group. The helper
`IsTransporter.baseChangePointsEquiv` proves its transporter equation on every
original test scheme: a refinement to the mapped test scheme equips that test
with a compatible structure over the new base; the existing point equivalence
then transfers the equation back, and the underlying identity comparison
reflects the result. This helper needs no hypothesis on the base change.

Three identity-component helpers place the image in the correct open.
`image_underlyingSet_baseChange` sends the relative identity set under the actual
pullback projection into the original relative identity set. It uses
functoriality of section-selected fibre components and the equality of that
component union with the relative identity set at the unit; it needs no
smoothness assumption. For a smooth affine field group,
`identitySet_subset_underlyingSet` applies the all-test criterion to the
geometrically connected actual identity-component inclusion.
`image_identitySet_baseChange` combines these results for any field pullback of
a smooth affine group.

After giving `k` the algebra structure determined by `b`, the published
`exists_relativeTransporter_factor_iff` factors the field point through the
actual affine transporter scheme. Its image over `s` lies in the inverse image
of the original relative identity set. That inverse image is an open subscheme,
since `RelativeIdentityComponent.isOpen_underlyingSet` proves openness for a
smooth group. It is smooth over the base by
`smooth_relativeTransporterScheme` and restriction to the open. The published
`Langlands.AlgebraicGeometry.exists_etale_spec_of_smooth` now constructs an
affine etale neighbourhood of the image of this source point together with a map
to that open. Composition with its inclusion and the universal transporter map
produces `pointMap`. Restriction of the universal all-test equation gives the
transporter property, and membership in the open gives relative identity
membership.

Finally, `inRelativeIdentityComponent_of_baseChangePointsEquiv` proves the
relative identity claim for the actual section after etale base change. It
factors the original point map through a representative from `smoothStructure`,
pulls that factor across the point adjunction, and uses the published arbitrary
base-change compatibility of the representative. The other section equations
follow from multiplicativity and naturality of the same point adjunction.

The provenance is internal. The construction combines the published actual
smooth transporter, relative identity-component structure, pullback-point
adjunction, and unpointed smooth etale local-section theorem. It supplies the
local lifting step requested for the openness argument. It does not construct
the initial field transporter or prove the host openness proposition.
