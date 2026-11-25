# Rational-point injectivity through affine scalar-quotient pullbacks

This module supplies a proved algebraic construction and a
conditional analytic reduction for `SpaceAnalytificationRationalPointsStatement`.
It does not prove that statement's full Hausdorff and topological embedding
target, which `spaceAnalytificationRationalPoints` (module
`SpaceAnalytificationRationalPointsProof`) proves.

## Algebraic construction

`exists_closed_affine_rationalPoint_pullback` constructs the represented
pullback of two `K`-points of a separated algebraic space. The map from this
pullback to the product of their representing ground-field spectra is a
closed immersion by the diagonal condition. The structural map of `Spec K`
over itself is the identity; consequently the first projection of its
self-product is an isomorphism. Composing gives a closed immersion of the
pullback into `Spec K`. In particular the pullback is affine. Its two maps
to the ground-field spectrum and its presheaf pullback square are retained.

`HasScalarQuotientRationalPointPullbacks` records the following property:
for every pair of rational points, there is a commutative `K`-algebra `C`
with a finite polynomial presentation, surjective scalar map `K → C`,
and a presheaf pullback square whose two maps to the ground-field spectra
are the spectra of this scalar map.

`hasScalarQuotientRationalPointPullbacks_of_isSeparated` proves this property.
Take the actual global sections of the affine pullback with the algebra
structure induced by its structural morphism. The closed immersion makes
the global-section map surjective; the canonical global sections of
`Spec K` identify this with surjectivity of `K → C`. Closed immersions
are locally of finite type, so the existing affine-scheme construction
supplies a finite polynomial presentation. The canonical affine scheme
isomorphism transports the presheaf pullback to `Spec C`. Both maps to
`Spec K` agree with the spectrum of the scalar map, because every map to
the identity object in the slice is uniquely determined by its base equation.

These algebraic declarations use the existing nontrivially normed-field
API for `pointHom`; their proofs are algebraic. No local finite type
hypothesis on the algebraic space is needed.

## Conditional analytic reduction

`rationalPoint_injective_of_pointLifting` assumes the explicit point-lifting
property for all categorical analytic pullback squares over the fixed `K`,
in the same field, space and index universe as
`SpaceAnalytificationRationalPointsStatement`. The property says
that any pair of ordinary points with equal image has a point of the given
pullback with those two projections. It asserts neither uniqueness of
such a point nor a topological pullback universal property.

The theorem proves that `rationalPoint p P₀` is injective for every
`IsAnalytification K X Y p` of a separated `X` and every presentation `P₀`
of `K`. First use the algebraic scalar-quotient pullback just constructed.
The `IsAnalytification.isPullback` condition gives its analytic pullback.
If two rational points have the same image, the point-lifting premise
gives an analytic point of `Spec C`. Its multiplicative seminorm takes
`0` to `0` and `1` to `1`, so `C` is nontrivial. The surjective scalar
map from the field `K` is therefore also injective. Its algebra inverse
provides a section of `Spec C → Spec K`. Precomposing the equality in
the presheaf pullback square by this section identifies the two maps
`Spec K → X`. The lifted Yoneda equivalence identifies the original
rational points.

The point-lifting property remains a genuine explicit premise of this
theorem; the Library proves it separately as `exists_point_of_isPullback`
(module `LocalizedPullbackPoints`). No
Hausdorffness, local finite type, rational-point naturality or analytic
étale local-isomorphism premise is used in this injectivity reduction.
The theorem does not assert continuity, the inducing property, or a
field-point surjectivity result.

## Provenance

This is internal deduction from published Library constructions and
Mathlib. It uses the represented pair pullback, the closed-diagonal
comparison in `AffineIntersections`, the affine closed-immersion and
global-section facts, the actual affine-coordinate presentation and
canonical scheme isomorphism in `AffineSchemeAnalytification`,
`IsAnalytification.isPullback`, `pointSeminorm`, and elementary field
and algebra-map facts. No external statement is newly translated.
