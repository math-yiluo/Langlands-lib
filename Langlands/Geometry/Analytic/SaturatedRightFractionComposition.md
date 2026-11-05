# Constructed Ore composition of actual saturated fractions

This is an internal construction from the existing retained-chart Ore source,
full quasi-isomorphism multiplicativity, and the actual saturated atlas
localization. The imported fraction equality and hom equivalence come from
`SaturatedLocalizedFractions`. No new assertion from an original geometric
source is attributed here.

## Objects and hypotheses

Fix a complete ultrametric normed field `K : Type u`. Objects `A`, `B`, `C`
and `D` are in `SaturatedAtlasPresentation.{u,v,w} K`, with independent ambient
space and chart-index universes `v` and `w`. Each contains an actual affinoid
atlas presentation and proved full-domain closure. Charts use actual finite
positive-polyradius Tate quotient algebras. Morphisms are complete strong maps,
with their continuous ambient map and bounded pullbacks at every admissible
original-chart pair. Composition is the existing saturated strong composition.

Write `W := quasiIsomorphisms` and `Q := localizationFunctor`. Membership in
`W` requires an ambient homeomorphism and the full `Represents` condition at
every admissible chart pair, including unique bounded factorization over every
presented-affinoid test algebra. The localization is the previously constructed
path-and-relations category. Its right calculus has already been proved from
constructed Ore sources and complete bounded-test cancellation.

A right fraction `φ : W.RightFraction A B` has source `S := φ.X'`, denominator
`s := φ.s : S → A` with `φ.hs : s.IsQuasiIso`, and numerator `f := φ.f : S → B`.
For `ψ : W.RightFraction B C`, write `T := ψ.X'`, `t := ψ.s` and `g := ψ.f`.
Its interpretation is `localizedRightFraction φ = Q(s)⁻¹ ≫ Q(f)`.

## The actual composite representative

Apply the already constructed Ore source to `f : S → B` and `t : T → B`.
It supplies an actual saturated retained-chart source `R`, complete arrows
`a : R → S` and `b : R → T`, a proof that `a` is a full quasi-isomorphism,
and the complete square

```text
b ≫ t = a ≫ f.
```

The source is constructed from the original atlas data; no output source,
square or lift is supplied as a new premise. `rightFractionComp φ ψ` is the
actual right fraction with source `R`, denominator `a ≫ s`, and numerator
`b ≫ g`. The denominator is a full quasi-isomorphism by the existing
multiplicativity theorem. All these arrows retain their entire bounded
pullback families, and the square is an equality of complete strong maps.

The exact ambient map of `a` is the identity on the space of `S`. Therefore
`rightFractionComp_s_baseMap` states that the composite denominator's ambient
map is exactly `s.baseMap`. The exact ambient map of `b` is
`t`'s inverse homeomorphism after `f.baseMap`, so
`rightFractionComp_f_baseMap` states

```text
(rightFractionComp φ ψ).f.baseMap
  = g.baseMap.comp (ψ.hs.inverseBaseMap.comp f.baseMap).
```

These statements identify continuous maps, not only their values on points.

## Interpretation and refinement invariance

`localizationFunctor_map_s_comp_localizedRightFraction` records the
inverse-denominator cancellation identity

```text
Q(s) ≫ localizedRightFraction φ = Q(f).
```

It is the imported right-fraction identity specialized to this localization.
`localizedRightFraction_comp` proves

```text
localizedRightFraction (rightFractionComp φ ψ)
  = localizedRightFraction φ ≫ localizedRightFraction ψ.
```

The implemented proof cancels precomposition with the invertible map
`Q(a ≫ s)`. On the left, the displayed cancellation identity leaves
`Q(b ≫ g)`. On the right, functoriality and cancellation of `Q(s)` leave
`Q(a ≫ f) ≫ localizedRightFraction ψ`. The complete Ore square replaces
`a ≫ f` by `b ≫ t`; functoriality and cancellation of `Q(t)` then give the
same `Q(b ≫ g)`. Thus the theorem uses the actual square, not an assumed
formula defining composition in the localization.

`localizedRightFraction_ofHom` further specializes the imported identity for
a fraction with literal identity denominator: its interpretation is `Q(f)`.

The existing `FractionCommonRefinement` compares two actual fractions by an
actual common source and complete equalities of their denominators and
numerators, with the common denominator a full quasi-isomorphism.
`fractionCommonRefinement_comp` proves that a common refinement of each
factor gives a common refinement of the constructed composites. The proof
uses the exact localized equality criterion, the interpretation theorem, and
congruence of categorical composition. This establishes existence of a full
common refinement; it does not specify a canonical refinement source.

## Composition on the hom quotients

`rightFractionQuotientComp` descends the actual `rightFractionComp` operation
by `Quotient.map₂`, using the proved refinement invariance. Its formula on
representatives is `rightFractionQuotientComp_mk`. The already constructed
`rightFractionHomEquiv` from the common-refinement quotient to a localized
hom set preserves this composition by `rightFractionHomEquiv_comp`.
The proof is quotient induction followed by `localizedRightFraction_comp`.

`rightFractionQuotientId A` is the class of the fraction whose denominator
and numerator are both the literal identity of `A`.
`rightFractionHomEquiv_id` proves that it maps to the localized identity.
The left identity, right identity and associativity laws are respectively
`rightFractionQuotientId_comp`, `rightFractionQuotientComp_id` and
`rightFractionQuotientComp_assoc`. Their implemented proofs apply the
injective hom equivalence and use the corresponding existing category laws.
These laws describe the actual descended operation; they do not assume
category laws as input data.

`rightFractionComp_assoc_commonRefinement` also states directly that the two
iterated actual composite representatives have a full common refinement.
It follows from the equality criterion, interpretation of composition and
associativity. No definitional equality of their retained-chart sources is
claimed. This unit equips the computed hom quotients with composition and
identities; it does not introduce a replacement localization category.

## Underlying continuous maps and remaining scope

`localizedSpaceFunctor_map_rightFractionComp` proves that the underlying
continuous map of the interpreted actual composite is

```text
TopCat.ofHom ((g.baseMap.comp ψ.hs.inverseBaseMap).comp
  (f.baseMap.comp φ.hs.inverseBaseMap)).
```

The proof rewrites by the interpretation theorem, uses functoriality, and
substitutes the previously proved continuous-map formula for each factor.
This is the composite of their actual numerator-after-inverse-denominator
continuous maps, with the same order as categorical composition.

The unit constructs fraction composition in the existing saturated
presentation localization. Comparison with an independently specified
Berkovich analytic-space category, etale, quasi-etale and equivariant sites,
compact and distinguished domains, and the Harris tower specializations
remain obligations of the surrounding task. The preceding fraction and Ore
units retain their independent acceptance and publication gates.
