# Point comparison for original Harris raw restriction

This internal construction proves compatibility of actual point transport and
actual restriction on the supplied Harris polarized family. It uses the
published `HarrisIntegralCMRestrictionFrames`,
`HarrisIntegralCMLevelPointComparison`, and Tate `WeilPathBaseChange`
constructions. It makes no new assertion from external literature.

## Data and scope

The universe-zero arithmetic data, central simple unitary algebra, Harris
signature charts, named `Prerequisites`, supplied abelian scheme `B`, dual
witness `W`, dual-valued morphism `lam`, and integral action `a` are the
existing ones. The original family over a test `T` is the direct pullback
along `T.hom`. The relative finite Weil transition statement and rational
profinite-integer adele comparison remain explicit.

All tests used here are quasi-separated. Point transport retains the torsion
finite-etale statement, invertibility of every indexed torsion order on its
test, and finite-etale roots of unity on that test. Its endpoints are actual
field-valued points with finite-fibre witnesses for all finite etale covers.
The fields may differ. The input path is an actual isomorphism of their
finite-cover fibre functors. Neither algebraic closedness, connectedness, nor
local Noetherianity is required once such a path is supplied.

For restriction, `f : T' → T` is an actual slice morphism over the original
base. Its two source points are `t` and `u`; the base points are literally
`t ≫ f.left` and `u ≫ f.left`. All four finite-fibre witnesses, the invertible
orders, and the finite-etale root-of-unity instances on both tests remain
explicit. No finiteness or etaleness premise on `f` is used. The restricted
integral action is literally `(relativeEndRestrict B f).comp a`.

## Actual raw point transport

`harrisIntegralCMWeilRawPointEquiv` descends the existing actual
`weilAdelicFrameTransport` through `RightOrbit.equiv`, using its proved
right-equivariance. It is defined for every subgroup of the original finite
adelic source-similitude group. Thus it acts on all raw right-orbit classes;
no monodromy fixedness premise is imposed on its input. This raw equivalence
retains its supplied path. The opposite-group convention of the original
right precomposition action is unchanged.

`harrisIntegralCMWeilRawPointEquiv_mk` identifies the map on an actual frame
representative by definitional equality.
`harrisIntegralCMFullActionLevelPointIso_raw` identifies the underlying raw
class of the existing original fixed-level point isomorphism with precisely
this raw point equivalence. This equality is also definitional. The original
fixed-level comparison already has its published path-independence theorem;
this contribution does not assert path independence for arbitrary raw
classes.

## Restriction and point transport

`harrisIntegralCMRestrictionFrameEquiv_pointMap` proves the actual frame
square: evaluate along `f` after transporting along a path on `T'`, or first
evaluate at `t` and then transport along its actual `pathPushforward` on `T`.
Both routes give the same frame at `u ≫ f.left`.

Subtype and linear-equivalence extensionality reduce the proof to every
actual rational Tate value. The published restriction value formula is the
actual `rationalHomMap` for `homToHom0` of
`relativeBaseChangeComparisonIso B f`, followed by actual
`rationalBaseChange f.left`. Naturality `rationalTransport_homMap` moves the
source path through that actual family homomorphism.
`rationalBaseChange_transport` then identifies the remaining transport with
the pushed path on the base. No compatibility square is supplied as an
extra premise.

`harrisIntegralCMRestrictionRawEquiv_pointMap` descends this frame square to
all raw right-orbit classes. Quotient induction reduces it to a frame
representative, and congruence of `RightOrbit.mk` applies the preceding frame
square.

`harrisIntegralCMRestrictionRawClass_pointMap` is the square for the existing
original raw evaluation of an actual fixed level. The published equality
`harrisIntegralCMRestrictionRawClass_eq_rawEquiv` identifies both original
evaluations with their actual frame-derived raw equivalences. The proved
underlying-class formula for the original point isomorphism and the raw
square then give the result.

`harrisIntegralCMFullActionLevelRestriction_pointMap` proves the corresponding
square for the unchanged original fixed-level restriction map. Apply the
injective actual raw evaluation equivalence to the underlying output classes.
The published `harrisIntegralCMFullActionLevelRestriction_rawValue` recovers
the original base classes, and the raw square proves their equality. Subtype
extensionality recovers equality of the actual fixed levels.

`harrisIntegralCMFullActionLevelRestriction_point_naturality` states this as
an equality of natural transformations between the original towers. In
composition order, base point transport followed by restriction at `u`
equals restriction at `t` followed by source point transport. Extensionality
in an original Harris level and its fixed-level element reduces it to the
preceding elementwise theorem. Thus the square respects all original level
transporters through the existing natural transformations.

These are compatibility results for a supplied family and supplied paths.
They do not construct paths, compare arbitrary rational-isogeny moduli
representatives, or construct a representing PEL scheme. The full normalized
presheaf comparison, determinant/Lie and Rosati integration, output
admissibility, smoothness, and division-case projectivity remain host
obligations. `DivisionCMRepresentabilityStatement` and all imported
Lean/Markdown pairs are preserved.
