# Nearby cycles on the strict target trait

Write `S = Spec R` for the arithmetic target and use the fixed `S^nr` of
`StrictTargetTrait`. SGA 7 XIII, (1.3.2.1)–(1.3.2.2), p. 94, gives the
geometric fibre diagram and transport of structure over `S̄`, the
normalization in `Ω_s` of (0.2.5), p. 86. The geometric points factor through
`S̄ → S^nr`, where `S^nr` is the pointed strict henselization of
(2.1.3)–(2.1.4), p. 100. Laumon (1987), (2.1.1), p. 151, describes this
strict trait and its geometric points.

For a chart `X → S`, `strictChart` is `X^nr = X ×_S S^nr`.
`strictChartModel` forms both fibres over this strict chart, with generic field
`K^nr` and special ring `R^nr/(t)`. `traitNearbyModel` applies
`NearbyCyclesModel.galoisLayer` to extend the generic fibre along the chosen
factorization `Spec Ω_s → Spec K^nr → S^nr`. The maps `ε` and `j` are the
same arrow to `X^nr`, and the model uses the special fibre over `R^nr/(t)`.

For a complex `B` on `X`, `strictChartPullback` is its derived pullback `B^nr`
and `chartNearbyCycles` applies `NearbyCyclesModel.nearbyCycles` to `B^nr`.
This is `Li* Rj_* Lε*` in the derived category of pro-étale module objects
with condensed coefficients. `arithmeticNearbyStalk` takes the derived
pullback along a point `x` of the special fibre. `arithmeticNearbyStalkComplex`
takes derived coefficient sections of this pullback via `Spec ℤ`. These are
the condensed model and coefficient complex of the stalk in SGA 7 XIII,
(2.1.1)–(2.1.2.3), pp. 98–99.

## Strict-local formula

`strictLocalGenericFibre` is the pullback of `j` to the strict localization of
`X^nr` at the geometric point underlying `x`. `strictNearbyStalkRestriction`
uses the pullback square with `j` to restrict the nearby stalk to
`strictLocalNearbyGerm`. The latter is the closed stalk of the direct image
from that local generic fibre. `strictLocalNearbyGermMap` uses the derived
adjunctions to map the coefficient cohomology of the local generic fibre to
the coefficient complex of the germ.

`StrictNearbyStalkFormulaStatement` asserts that both maps are invertible.
The first comparison is on the pro-étale category of the geometric point.
Applying derived coefficient sections to it and using the second comparison
identifies the nearby stalk complex with the local generic cohomology complex.
The statement takes finite discrete commutative coefficients in which the
characteristic of the finite ground field is invertible. It uses bounded below
input of étale origin, as expressed after the finite-coefficient derived
equivalence. This is the strict-local formula of SGA 7 XIII, (2.1.3) and
Proposition (2.1.4), p. 100, with the comparison expressed by canonical arrows
in the condensed model. The construction applies to Laumon's Fourier charts
in (2.3.2)–(2.3.3), pp. 159–161. His (2.4.2)–(2.4.2.1), p. 162, gives the
three local Fourier charts and compares the vanishing-cycle complexes by
pullback.

## Arithmetic Galois action

For `σ ∈ Gal(Ω_s/K')`, `traitNearbyModelGalois` forms the three scheme maps
from the restrictions to `R^nr`, `Ω_s` and `R^nr/(t)`. These maps are over the
arithmetic chart when `σ` fixes the image of its base ring. For `R` itself
this equality is `strictRingGalois_comp_endStrictRingHom`.
`nearbyCyclesAction` composes `NearbyCyclesModel.Hom.pullbackExchange`, the
model's inverse-image comparison as in SGA 7 XIII, (2.1.7.2), p. 101, with the
pullback identification of `B^nr` furnished by the projection to `X`.
It gives an arrow from the pullback of nearby cycles under the special-fibre
map to the original nearby cycles. `arithmeticNearbyStalkMove` pulls this
arrow back along `x` to carry the stalk at the translated geometric point
back to the stalk at `x`. A compatible endomorphism of the point's ring gives
`arithmeticNearbyStalkTransport` on its fibre category.
`arithmeticNearbyStalkAction` transposes the transport across the adjunction
over `Spec ℤ` and takes derived coefficient sections. At the lift
`rationalStrictChartPoint` of a rational special point, the residue map supplies
the compatible endomorphism canonically for every `σ`.

`NearbyStalkGaloisStatement` asserts invertibility of the exchange on the
nearby cycles and of the induced moving-stalk map. It states the unit and
composition laws and naturality in `B`. At points with compatible maps of the
point's ring, it records the composition and coefficient action laws.
`RationalNearbyStalkGaloisStatement` is its clause for the entire group on the
coefficient complex at a lifted rational point. The convention is
`act (σ * τ) = act τ ≫ act σ` on the coefficient complex. For inertia the
special-fibre map becomes the identity, and the action is the imported
`NearbyCyclesModel.galoisLayerAction` for `Ω_s/K^nr`, with the derived identity
pullback comparison. These laws realize the transport of structure of
SGA 7 XIII, (1.3.2.2), p. 94, on the chart over the pointed strict
henselization used in Laumon, (2.1.1), p. 151.

## External declarations

At weil-conjectures commit `a25955cde4f85f67bef3149a6efc3efe20c22132`,
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for each
of the following declarations. Names of model and condensed operations
below are in `AlgebraicGeometry.ProEtale.CondensedRing`.

- `NearbyCyclesModel`, `NearbyCyclesModel.mk`, `.i`, `.j`, `.ε`, `.Hom`,
  `.Hom.mk`, `.Hom.comm_i` and `.nearbyCycles` are from
  `SixFunctors.NearbyCycles.Basic`.
  `NearbyCyclesModel.galoisLayer`, `.galoisLayerAction` and
  `.Hom.pullbackExchange` are from `GaloisLayer`, `GaloisAction` and `Exchange`
  in the same folder.
- `upperStar` and `lowerStar` in `SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
  and `CategoryTheory.Functor.leftDerivedFunctor` and `.rightDerivedFunctor`
  give the pullbacks and direct images denoted by `L` and `R`.
  `derivedUpperStarLowerStarAdjunction` and `leftDerivedUpperStarComp` are
  from `ModuleObject.Derived.UpperLowerStar`. `leftDerivedUpperStarCompOfEq`
  and `leftDerivedUpperStarId` use `NearbyCycles.HomComp` and
  `ModuleObject.Derived.UpperStarCoherence`, respectively. `baseChangeMap`
  from `ModuleObject.Derived.Localizing` gives the restriction to the germ.
- `AlgebraicGeometry.Scheme.strictLocalization`, `.strictLocalizationToBase`,
  `.strictHenselizationEval` and
  `.spec_map_strictHenselizationEval_comp_strictLocalizationToBase` from
  `AlgebraicGeometry.Sites.StrictHenselizationLocal` give the strict
  localization and its pointed structure map.
- `AlgebraicGeometry.ProEtale.condensedRingObj`, `.specZ`, `.toSpecZ` and
  `.comp_toSpecZ` from `SixFunctors.ProEtale.ModuleObject.Basic` give the
  coefficient objects and the structure map. `condensedRingCoefficientSections`
  and `condensedRingOrdinaryCoefficientComplex` from
  `ModuleObject.Derived.CondensedOrdinaryCompactCohomology` form the coefficient
  sections and cohomology complexes.
- `Profinite.continuousMapRingObj`,
  `AlgebraicGeometry.ProEtale.finiteCoefficientDerivedEquivalence` and
  `AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin` specify the
  finite coefficient object and the étale-origin hypothesis.
- `CategoryTheory.sfbRegularAbMonoidal` and `CategoryTheory.sfbRegularAbSymmetric`
  are the monoidal instance names used in the elaboration attribute.
  `HasDerivedCategory.ofIsGrothendieckAbelian` from
  `CategoryTheory.GrothendieckAbelian.HasDerivedCategory` is the local
  derived-category instance.

The coefficient category uses Mathlib's `AlgebraicGeometry.Scheme.ProEt.topology`,
with `[propext, Classical.choice, Quot.sound]`, and `CategoryTheory.Mod`,
which has no axiom dependencies.
