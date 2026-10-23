# Geometry and base change of the unitary group schemes

Author: Worker 57.

This module constructs the pullbacks of the existing similitude and unitary group
schemes to any scheme over the coefficient ring. It proves finiteness, affineness
of the structure maps, separatedness and Noetherian properties. It also recovers
the algebraic points of these pullbacks, including restriction, multiplier and
unitary-inclusion formulas. The rational specialization applies to the existing
central simple CM algebra datum.

## Internal provenance and scope

This is an internal derivation from `RationalGroupScheme`, `UnitaryGroupScheme`,
the finite presentation of the explicit coordinate algebra in
`SimilitudeCoordinates`, the actual group-scheme pullback and point adjunction in
`AbelianScheme.KernelBaseChange`, and the multiplicative-group base-change
isomorphism in `GroupScheme.Multiplicative`. The geometric deductions use
Mathlib's `Morphisms.FinitePresentation`, `Morphisms.Affine`,
`Morphisms.ClosedImmersion`, `Morphisms.Separated` and `Noetherian` APIs. No new
external existence theorem is invoked. The arithmetic and involution conventions
are inherited without modification from the imported modules.

The generic input is a commutative ring `R`, a possibly noncommutative `R`-algebra
`A`, a finite basis `b` and an algebra involution `σ`. The ring, algebra, basis
index and schemes lie in the same universe. The new base is an arbitrary scheme
`S` with a morphism `f : S ⟶ Spec R`. The point comparisons allow every scheme
`T` over `S`, including nonaffine schemes. Affineness here is a property of the
structure morphism to `S`; the total pullback need not be affine when `S` is not.

The unitary finite-presentation results require the original ring `R` to be
Noetherian. This requirement applies to `R`, not to `S`; in particular it holds
for every rational base change, even when the new base is not Noetherian.
Noetherian conclusions for the total scheme separately require the corresponding
Noetherian condition on `S`. This contribution does not identify the pullback
with a new coordinate model formed over another coefficient ring. Smoothness,
reductivity, real-model comparison, Harris PEL representability, scheme levels
and coefficient descent remain outside these declarations.

## Finiteness before base change

`groupScheme_locallyOfFinitePresentation` rewrites the actual structure map as
`Spec.map` of the inclusion of `R` into `σ.similitudeCoordinateRing b`. The
spectrum criterion reduces the claim to finite presentation of that ring map,
then to the already proved finite presentation of the coordinate algebra.

`unitaryGroupScheme_locallyOfFiniteType` uses the commuting triangle of
`unitaryInclusion`: the unitary structure map is the closed immersion into the
similitude scheme followed by its structure map. Closed immersions are locally
of finite type, and that property is preserved under composition. If `R` is
Noetherian, `Spec R` is locally Noetherian, so Mathlib's finite-type criterion
supplies `unitaryGroupScheme_locallyOfFinitePresentation`.

## Actual pullbacks and their geometry

`baseChangedGroupScheme b σ f` and `baseChangedUnitaryGroupScheme b σ f` apply
`GroupScheme.baseChange f` to the existing group schemes. Their underlying
structure maps are the second projections of scheme pullbacks. Thus the output
schemes, their group structures and their structure morphisms are constructions,
with no additional representability premise.

The two `baseChanged..._isAffineHom` instances apply stability of affine
morphisms under base change. The original source and target are affine, so their
structure maps are affine. Local finite presentation of the similitude map and
local finite type of the unitary map are also preserved under base change. If
`R` is Noetherian, the unitary pullback likewise has a locally finitely presented
structure map. The two `baseChanged..._isSeparated` instances follow from the
affine-morphism criterion for separatedness. Affine morphisms are also
quasi-compact.

If `S` is locally Noetherian, each total pullback scheme is locally Noetherian
because its structure map is locally of finite type. If `S` is Noetherian, the
same local conclusion and quasi-compactness of the structure map make the total
scheme compact, giving the two `baseChanged..._isNoetherian` instances.

## Points, coefficients and morphisms

For a test scheme `T` over `S`, write `T_R` for `(Over.map f).obj T`. Its
structural map is the composite `T ⟶ S ⟶ Spec R`. Let `B_T` denote
`((algΓ (CommRingCat.of R)).obj T_R).unop`: this is the algebra of global
sections with the `R`-action induced by that composite.

`baseChangedPointsEquiv b σ f T` is a multiplicative equivalence from points of
the similitude pullback to `(σ.baseChange B_T).similitudes`. It composes the
multiplicative pullback adjunction with the original `pointsEquiv`. Thus the
recovered element uses the original tensor extension `B_T ⊗[R] A`; it does not
replace the structural action by an arbitrary algebra structure.

For `a : T' ⟶ T`, `baseChangedPointsEquiv_naturality` says that precomposition
by `a` corresponds to `σ.baseChangeMap` of the algebra map obtained by applying
`algΓ` to `(Over.map f).map a` and removing the opposite. The proof composes
the naturality of the pullback adjunction with the existing similitude
naturality formula; the remaining equality is definitional.

`baseChangedMultiplier` is the actual base-changed multiplier followed by
`Gm.baseChangeIso f`, with target the multiplicative group over `S`.
`baseChangedMultiplier_points` proves that postcomposition with this morphism
recovers exactly the scalar multiplier of `baseChangedPointsEquiv` as a unit of
global sections. The proof uses the point formula for the multiplicative-group
base-change isomorphism, compatibility of the pullback adjunction with group
homomorphisms, and the original multiplier formula.

`baseChangedUnitaryPointsEquiv` similarly composes the pullback adjunction with
`unitaryPointsEquiv`, giving a multiplicative equivalence to
`(σ.baseChange B_T).unitary`. The naturality theorem identifies its underlying
unit after restriction with `Units.map` of the tensor coefficient map induced
by `a`. Both sides are ambient units obtained from the constructed unitary
point comparison, so this equality determines restriction on the unitary
subgroup. Its proof is the same composition of the two existing naturality
formulas.

`baseChangedUnitaryInclusion` is the base change of the actual unitary inclusion.
Its point theorem states equality in the similitude group: the original
algebraic inclusion of the recovered unitary element equals the recovered
similitude after postcomposition with the scheme inclusion. In particular,
this formula preserves the algebra unit and records multiplier one. The proof
uses the adjunction's compatibility with morphisms and the original inclusion
point formula.

## Rational specialization

`CentralSimpleUnitaryData.rationalBaseChange` and
`rationalUnitaryBaseChange` specialize these pullbacks to `D.rationalBasis` and
the rational restriction of the second-kind involution. They inherit the number
field and scalar-tower conventions of `RationalGroupScheme`; their fields and
algebra have small carriers. The rational basis is the already constructed basis
from the finite CM algebra, not an extra input.

`rationalBaseChanges_geometry` bundles, for both structure maps over any small
scheme `S ⟶ Spec ℚ`, affineness, separatedness, quasi-compactness and local finite
presentation. It uses the instances above and the Noetherian property of `ℚ`.
These properties give finite presentation in the usual sense: separatedness
implies quasi-separatedness, and quasi-compact plus quasi-separated plus locally
finitely presented is finitely presented. The Lean conclusion explicitly lists
the four properties for each map; it does not introduce a separate global
finite-presentation class.
