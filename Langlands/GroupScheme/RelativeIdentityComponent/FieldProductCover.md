# Products of open unit neighbourhoods cover the field identity component

For a smooth group scheme `H` over a field `k`, in any universe, this derived
helper defines the actual restricted multiplication map
`fieldOpenProduct H i = (i ⊗ₘ i) ≫ μ[H.X]` for a map `i : P ⟶ H.X`.
The public theorem `identitySet_subset_range_fieldOpenProduct` states that if
`i.left` is an open immersion and its range contains the unit point, the whole
identity component `IdentityComponent.identitySet H` is contained in the range
of this product map. The neighbourhood is arbitrary; its image need not itself
be contained in the identity component. There is no affineness, quasi-compactness,
or algebraic-closedness assumption.

The implemented proof first treats a rational target `x` in the identity
component. Let `σ` send `z` to `z⁻¹x`. The open neighbourhood and its inverse
image under `σ` both meet the identity component: the first at the unit, the
second at `x`. The noncircular irreducibility theorem from `FieldGeometry`
gives a point in their intersection. On the spectrum of that point's residue
field, both the canonical map and its composite with `σ` lift through `i`.
Their product is the constant map with value `x`, by the group law on the Hom
set. The residue spectrum has an actual point, so evaluation proves membership
in the range of the actual restricted multiplication map. These rational-case
factorization and image lemmas are private implementation helpers.

For an arbitrary target point `y`, lift it to a point `c` of the raw connected
component scheme `fieldIdentityOver H`. Base change to the residue field of `c`.
The base-changed component scheme is connected because its structure map is
geometrically connected and smooth, hence universally open. Its base-changed
unit section maps to the ambient unit. The canonical rational point above `c`
therefore maps into the identity component of the base-changed group, using
`IdentityComponent.range_subset_identitySet`. The open neighbourhood still
contains the unit after base change: its lifted unit section base changes using
the monoidal unit comparison. Apply the rational-case image lemma over this
residue field.

A private comparison identifies the image of the restricted multiplication
after base change with the inverse image of the original product image. It uses
the naturality of the monoidal tensor comparison, which is an isomorphism, and
the pullback image formula for schemes. Evaluating the canonical residue-field
point under the first pullback projection gives `y`, so the required image
membership descends. This image comparison adapts Worker 513's general
monoidal base-change argument.

The provenance is internal derivation from `FieldGeometry`, actual open-immersion
factorization, Mathlib's irreducible open-intersection property, the Cartesian
Hom group laws, geometric connectedness under pullback, and the scheme pullback
image formula from `BaseChange`. The component geometry is used before relative
openness is known. This helper does not prove the unconditional relative
openness or smooth structure statement; it supplies its field product-cover
step.
