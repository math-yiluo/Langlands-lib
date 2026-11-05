# Actual split-component realization of the enlarged KP building

This module constructs the enlarged product in the real cocharacter space of
an actual split component, and identifies it with the canonical rational-character
dual product. It works over `F : Type u` with the existing nonarchimedean local-field
structures, in either characteristic, and an actual group scheme `G` over `F`.
The product constructions require `[IsAffineHom G.X.hom]` and use one fixed
`B : ValuationBuildingData G`, including its same reduced quotient, apartment,
actual rational-point action, normalizer action and reduced fixers. The earlier
central-space definitions need no affine hypothesis. These are conditional
constructions over supplied data.

`SplitComponentComparison G` contains an actual commutative group scheme `A`,
an actual morphism `a : A.toGrp ⟶ G`, the existing `IsSplitComponent a`, and
`Function.Bijective (Cartan.restrictionEvaluation a)`. No comparison theorem is
assumed implicitly. The convenience constructor `ofIntegralInputs` uses the
splitness already contained in `IsSplitComponent`, explicit injectivity of
`characterRestrict a`, and its finite-index range to invoke the published real
comparison theorem. It does not prove these integral hypotheses.

For `C : SplitComponentComparison G`, the dedicated type `C.CentralSpace` is
`RealTorusSpace.V C.A`, with its actual additive group and real module. A separate
type name allows its translation action to coexist with other cocharacter actions.
`C.centralEquiv` is the real linear equivalence obtained from the actual
`Cartan.restrictionEvaluation C.a` using `C.bijective`, followed by the identity
identification with `CentralFactor G`. In particular `centralEquiv_apply`
identifies its underlying map with actual restriction evaluation.

## Source and provenance

The governing source is Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), §4.3, opening, Lemma 4.3.1, Definition 4.3.2 and Lemma 4.3.3, printed
pp.178–179 / PDF pp.209–210, together with §2.6(d), printed pp.102–103 / PDF
pp.133–134. Registered source: `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' *Corrections and additions* of 1 November 2024, PDF p.25, correct
the character valuation to have positive sign. Registered source:
`kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The relevant original passages and corrections were read directly.

The source defines the enlarged building as the reduced building times the
real cocharacter space of the split center, with negative character-valuation
translations. Here that cocharacter space is the actual published `V A`; its
identification with the rational-character dual is conditional on the visible
restriction-evaluation bijectivity. The source's reductive building setting is
represented by the supplied reduced data and split-component comparison.
The elementary product constructions use only those APIs, so the Lean does
not impose additional reductivity assumptions. The product comparison, maps,
translated-apartment identities and general nonempty pointwise-fixer formula
are internal derived constructions. The nonempty hypothesis makes explicit
an essential boundary of the source's subset stabilizer assertion.

## Actual central action and normalization

`C.translation` is a homomorphism to the multiplicative tag of `C.CentralSpace`,
with underlying additive value

```text
-(Cartan.centralizerValuation C.a C.bijective g).toAdd.
```

The existing valuation applies to this actual morphism; its name does not
restrict it to a centralizer inclusion. The action is `v + (C.translation g).toAdd`,
and `smul_eq` displays this as subtraction of the positive valuation.
`centralEquiv_valuation` unfolds the inverse linear comparison and cancels it
with restriction evaluation. It identifies the actual cocharacter valuation
with `rationalNormLogarithm G g`. Linearity gives `centralEquiv_translation`
and `centralEquiv_smul` for their negatives and affine actions.

`smul_eval` evaluates the action at `Cartan.characterRestriction C.a χ` and
uses the published `centralizerValuation_spec`. Its formula is exactly the old
coordinate minus the real cast of `(rationalCharacterValuation G g).toAdd χ`.
The imported specification uses the actual character evaluation and the
published `rationalNormLogarithm_eq_intValuation` normalization. Thus the
valuation is positive and the translation negative, as corrected by the authors.

`translation_ker` transports vanishing through the injective `centralEquiv`
and uses the canonical central translation kernel theorem. It equals the
existing `rationalCommonNormKernel G`, the source's `G(F)^1`.
`smul_eq_self_iff` cancels the old vector and `centralStabilizer_eq` applies
subgroup extensionality. Every central point therefore has this same actual
stabilizer.

## Products, apartments and comparison

`C.EnlargedBuilding B` is `B.ReducedBuilding × C.CentralSpace`, carrying the
diagonal actual `rationalPoints G` action. `C.EnlargedApartment B` is
`B.Apartment × C.CentralSpace`, carrying the product normalizer action.
`enlargedApartmentMap` applies the existing reduced apartment map on the first
coordinate and the identity on the second. Its normalizer equivariance uses
the existing reduced equivariance and equality on the central coordinate.
`enlargedApartmentMap_injective` explicitly requires injectivity of
`B.apartmentMap` and compares the two coordinates.

`enlargedEquiv` and `apartmentEquiv` are the product equivalences given by
identity on the reduced factor and `C.centralEquiv` on the central factor.
Their action compatibilities follow coordinatewise from `centralEquiv_smul`.
`enlargedEquiv_apartmentMap` is the commuting product-map identity.
`enlargedEquiv_translatedApartmentMap` combines it with equivariance.

The base apartment subset is the range of the actual product map. A translated
apartment subset is its actual group translate, also proved to be the range
of `enlargedTranslatedApartmentMap`. `enlargedTranslatedApartment_eq_prod`
identifies it with `(g • B.apartmentImage) ×ˢ univ`. In the reverse inclusion,
apply `g⁻¹` to the prescribed central coordinate to construct a preimage.
The identity element gives `enlargedApartmentImage_eq_prod`. These results
use no apartment-map injectivity hypothesis.

`enlargedProjection` takes the first coordinate. `enlargedZeroSection` appends
zero. Projection is equivariant, is a retraction of the zero section, and is
surjective with that section as witness. The zero section is equivariant for
the actual subgroup `rationalCommonNormKernel G` because it fixes zero in the
central factor. `centralTranslate v` adds `v` to the second coordinate.
Its zero and addition laws, projection invariance, and commutation with the
group action follow by additive identities. Equal projections are equivalent
to the existence of a central translation between points; the witness is the
difference of their central coordinates. The product comparison preserves
projection, zero section and central translations, using the zero and addition
laws of `centralEquiv`.

## Actual stabilizers and scope

`enlargedStabilizer` is the full Mathlib point stabilizer of the actual product
action. `enlargedPointwiseFixer` is `fixingSubgroup` of an actual subset, so it
fixes every point, rather than only preserving the subset as a set.
Equivariance and injectivity of `enlargedEquiv` identify both stabilizers with
the canonical product stabilizers, using the image subset for pointwise fixers.
The imported canonical subgroup equalities then give

```text
C.enlargedStabilizer B x
  = B.compactStabilizer (C.enlargedProjection B x)
  = rationalCommonNormKernel G ⊓ B.fixer (C.enlargedProjection B x).
```

The full stabilizer is consequently independent of the central coordinate.
For a nonempty subset `Y`, its pointwise stabilizer is the norm kernel
intersected with `B.pointwiseFixer (C.enlargedProjection B '' Y)`.
Composition of projection with `enlargedEquiv` is the original projection,
which gives the projection-image formula when transporting the canonical
pointwise-fixer equality. For nonempty reduced `Ω`, projection of
`Ω ×ˢ univ` is `Ω`, yielding the requested product-subset formula.
`enlargedPointwiseFixer_empty` separately records the whole group for the
empty subset. No nonempty assumption is omitted.

These are algebraic subgroup equalities. The name `compactStabilizer` comes
from the existing reduced API and asserts no topological property here.
This module proves no metric, bounded-subset assertion, compactness, openness,
parahoric comparison, full-torus splitting, choice independence, derived-point
annihilation, corrected building certificate, or general building existence.
Worker 1294 authored the split-component realization; it uses Worker 455's
canonical central-factor and enlarged-product modules and proof patterns.
