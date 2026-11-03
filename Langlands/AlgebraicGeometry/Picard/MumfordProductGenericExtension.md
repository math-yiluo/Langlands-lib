# Actual self-product extension from affine projectivity

This internal construction uses an arbitrary valuation domain `R`, the
supplied fraction field `K`, and a Library abelian scheme `A / Spec R`.
Its generic scheme is the actual self-product of the actual base change
`B / Spec K`. The map to the total self-product is exactly
`mumfordProductBaseChangeMap A (Spec.map (algebraMap R K))`,
the canonical product map appearing in
`ValuationRingTwoAxisExtensionStatement`.

The total self-product structure morphism is smooth, universally closed,
separated, and geometrically connected. The local instances prove these
properties by composition with the first product projection and the
corresponding properties of the abelian scheme.

`isPullback_mumfordProduct_generic` identifies the canonical product map
as a generic pullback of the actual total self-product structure morphism.
Its second projection is the canonical
`mumfordProductBaseChangeIso.hom` followed by the ordinary pullback's
second projection. The proof applies `IsPullback.of_iso_pullback` to
that actual scheme isomorphism. The required equalities are the published
first-projection identity and the ordinary pullback condition.
This cartesian-square result needs neither valuation nor fraction-ring
assumptions; it retains the given field and algebra structures.

`mumfordProduct_generic_app_injective` proves injectivity on actual
sections of every total open. The supplied fraction-field spectrum map
is scheme-theoretically dominant. The total self-product is flat over
the base, so its generic pullback projection is scheme-theoretically
dominant. Composition with the canonical scheme isomorphism preserves
this property. Quasi-compactness and
`Scheme.Hom.app_injective` then give the stated injectivity for the
exact canonical product map. No valuation hypothesis is needed for
this injectivity result.

`mumfordProductLineBundleExtension` retains
`AffineClosedFibreSectionProjectivity (mumfordProduct A).hom` as an
explicit hypothesis. Given any actual line bundle `D` on the generic
self-product, it constructs an actual line bundle on the total
self-product. It applies `lineBundleOfClosedFibreFrames` to the
cartesian square and injectivity just proved, and to the published
`mumfordProductClosedFibreGenericFrames K A D`.

`mumfordProductLineBundleExtensionIso` supplies the actual
module-sheaf isomorphism from the pullback of that total bundle along
the canonical product map to the original `D.obj`. It is the
`closedFibreFramesIso` from precisely the same construction.
Neither definition replaces the generic bundle by an abstract class.

`valuationRingTwoAxisExtension_of_integralFibreProjectivity` has type
`IntegralFibreProjectivityStatement.{u} →
ValuationRingTwoAxisExtensionStatement.{u}`.
Its only outer input is the explicitly supplied projectivity proposition.
For each `R,K,A`, the adapter in `ProjectiveGenericExtension` turns this
input into the required projectivity of the actual affine section
algebras. The preceding two definitions then give the exact bundle and
isomorphism required by the published target. Their construction works
for every `D`, so the target's two axis-triviality premises are unused.

The provenance is internal: this module specializes and composes the
published self-product base-change isomorphism, generic frame cover,
sectionwise injectivity criterion, and the conditional generic extension
construction. The conditional theorem is not an unconditional proof of
the two-axis extension statement. It does not prove or assume as an
instance the separate integral-fibre projectivity proposition; that
proposition occurs as an explicit argument. All universes, valuation
ranks, and supplied fraction fields remain unrestricted.
