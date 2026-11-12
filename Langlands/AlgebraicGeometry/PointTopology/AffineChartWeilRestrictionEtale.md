# Étaleness of affine-chart Weil restrictions

Author: Worker 185.

This module supplies one local input for the affine-atlas step in Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Lemma 5.10, printed pp.17–18 (registered source
`conrad-2011-weil-grothendieck-adelic-points`). Conrad uses that restriction
of scalars along a finite locally free extension preserves étale morphisms.
Here this is proved for the Library's algebra-level and glued scheme-level
Weil restrictions; the proof route is the standard infinitesimal-lifting one
and is not copied from the source.

Throughout, `B` is a finite projective algebra over an arbitrary commutative
ring `A`.

## Algebra

`Langlands.Algebra.weilRestriction_formallyUnramified` states that for a
finitely presented, formally unramified `B`-algebra `C`, the TauCeti Weil
restriction `WeilRestriction A B C` is formally unramified over `A`. The proof
uses the criterion `Algebra.FormallyUnramified.iff_comp_injective`: given an
`A`-algebra `T` with a square-zero ideal `I` and two `A`-algebra maps out of
the Weil restriction that agree modulo `I`, transport them by the Weil
restriction adjunction `WeilRestriction.homEquiv` to `B`-algebra maps
`C → B ⊗[A] T`. The kernel of `B ⊗[A] T → B ⊗[A] (T ⧸ I)` is the extended ideal
`Ideal.rightTensorIdeal A B I`, whose square is the extension of `I ^ 2 = ⊥`,
hence zero. Formal unramifiedness of `C` over `B`
(`Algebra.FormallyUnramified.lift_unique'`) then makes the two transported maps
equal, and `homEquiv` is injective.

`weilRestriction_etale` combines this with the published formal smoothness of
the TauCeti Weil restriction to get `Algebra.Etale A (WeilRestriction A B C)`
for étale `C`. `weilRestrictionFiniteType_etale` transports étaleness to the
Library's finite-type model `WeilRestrictionFiniteType A B C` through
`WeilRestrictionFiniteType.finitePresentationAlgEquiv`.

## Schemes

`affineCoordinate_etale` states that the coordinate ring
`AffineCoordinateRing R U` of an affine étale scheme `U` over `Spec R` is an
étale `R`-algebra; it reads the property through
`HasRingHomProperty.Spec_iff` and the identification
`affineCoordinateSpecMap`.

The instance `affineWeilRestriction_etale` states that for an affine scheme `X`
over `Spec B`, locally of finite type and étale, the structure morphism of
`affineWeilRestriction A B X` to `Spec A` is étale: that scheme is the spectrum
of the finite-type Weil algebra of the coordinate ring.

`openOver_etale` records that an open subscheme of an étale scheme is étale
over the base. The instance `affineChartWeilRestriction_etale` states that for
any scheme `Y` over `Spec B` that is locally of finite type and étale, the
glued scheme `affineChartWeilRestriction A B Y` is étale over `Spec A`. Étaleness
is local on the source, and the glued scheme has the open cover
`affineChartWeilRestrictionOpenCover` by the affine Weil restrictions of the
affine opens of `Y`, each of which is étale by the previous instance.

The module claims no surjectivity and no representability statement.
