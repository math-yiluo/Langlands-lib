# Base naturality of actual integral Harris compatible families

This internal unit constructs actual restriction into the existing compatible
family of normalized CM classes at all geometric points and proves its
base-change square. It retains the universe-zero Harris CM arithmetic data,
abelian scheme `B` over `S`, supplied dual witness and polarization, and morphism
`f : T' ⟶ T` of quasi-separated test schemes over `S`. Both test schemes are
connected and locally Noetherian in the family-square theorem. The supplied
full-order integral action on the direct family over `T` satisfies the joint CM
condition. The action over `T'` is literally
`(relativeEndRestrict B f).comp a`; the existing restriction theorem derives its
joint CM condition. The original source family has prescribed relative dimension.

The named `Prerequisites`, duality naturality, Lie base-change naturality on `T`,
finite Weil transitions, adelic comparison, torsion statement, and ordered-pair
dual-map additivity on both schemes remain explicit. Every positive order is
invertible and roots of unity are finite etale on each test scheme. The starting
point `v` is an actual `HarrisGeometricPoint T'.left`, so it has an algebraically
closed field. Its pushed point is `v.comp f.left` on `T`. The existing geometric
point theorem supplies finite fibres on finite-etale covers at both points.

`harrisIntegralCMFullActionLevelFamilyRestriction` first applies the actual raw
level restriction at `v` and then the existing integral-family transformation
to compatible geometric-point families on `T'`. It is a natural transformation
on the original Harris level category, from the lifted raw tower on `T` at the
pushed point to the compatible normalized-class family tower on `T'`. It
preserves the original fixed right-orbit and transporter conventions. Its
construction needs the target's connectedness and local Noetherianity; the
source instances are not needed for this definition.

`harrisIntegralCMFullActionLevelFamilyRestriction_evaluate` proves that evaluating
the resulting family at `v` gives exactly
`harrisIntegralCMFullActionLevelOriginalClassRestriction`. The proof unfolds
the two restriction composites, reassociates composition and applies the
existing family-evaluation law. Source connectedness and local Noetherianity
are omitted from this lemma as well.

`harrisIntegralCMFullActionLevelFamilyNatTrans_baseChange` proves that this
restricted family equals the family obtained by first constructing the
compatible family on `T` at `v.comp f.left` and then applying the existing
`geometricFamilyTowerPullback` along `f.left`. The latter uses the actual
structure triangle `f.left ≫ (T.hom ≫ p) = T'.hom ≫ p`. The result holds for any
constrained pulled dual-evaluation data on the actual ordinary pullbacks of
the source positive actions; it requires no supplied base-change square.

The proof cancels the target geometric-family evaluation isomorphism. The
restriction evaluation law, the generic family-pullback evaluation law, and
the source family evaluation law reduce the equality to the normalized-class
base-change square. The previously proved
`harrisIntegralCMFullActionLevelOriginalClassNatTrans_baseChange_dualData`
then supplies the result. Since the cancelled morphism is an isomorphism,
this proves equality of the full compatible families, naturally at every
original Harris level and transporter.

The provenance is internal: the construction composes existing actual raw
restriction and geometric-family maps, and the proof uses their evaluation
laws and the actual original-isogeny normalized-class square. This unit does
not construct a representing scheme or prove admissibility, smoothness or
division projectivity. Test-variable laws for the raw restriction and the
surrounding representability geometry remain separate obligations.
