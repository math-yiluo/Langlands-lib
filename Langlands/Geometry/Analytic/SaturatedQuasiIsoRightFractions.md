# Actual right fractions of saturated strong atlas maps

This is an internal packaging of the constructed compatible Ore refinement
in the existing saturated strong-map category. It cites no new external
assertion. The general calculus-of-fractions definitions are imported from
Mathlib; the geometric existence condition is proved using actual atlas
refinements rather than assumed as part of an abstract category interface.

## Actual category and full quasi-isomorphisms

Work over a complete ultrametric normed field `K : Type u`. Objects of
`SaturatedAtlasPresentation.{u,v,w} K` are actual affinoid atlas presentations
with ambient spaces in `Type v`, chart indices in `Type w` and proved
`HasAllLocalDomains`. This property means that every actual local full domain
has the locus of an original chart. The earlier saturation construction
produces such objects. Morphisms are actual strong maps retaining continuous
ambient maps and bounded pullbacks for every admissible chart pair. The
category uses the existing `saturatedComp`, including its full bounded
pullback family.

The morphism property `quasiIsomorphisms` is the existing full strong
quasi-isomorphism condition: the ambient map is a homeomorphism and every
admissible pullback satisfies the complete `Represents` predicate for its
chart-image locus. This includes unique bounded factorization for every
presented-affinoid coefficient algebra. The existing property is already
multiplicative. No directedness or upper-cofinality hypothesis is introduced.

## Actual saturated source and square

For arbitrary saturated maps `f : A → C` and `s : B → C`, assume only
`hs : s.IsQuasiIso`. The existing fully faithful `compatibleFunctor` gives
compatible strong maps without changing their underlying strong maps;
full source-domain closure proves their local compatibility.

`quasiIsoOreSource f s hs` wraps the actual source refinement constructed in
`CompatibleQuasiIsoOreRefinement`. Its proved full-domain closure supplies
the saturated-object field. It is a retained-chart subpresentation on the
literal space of `A`, with the original selected algebras and restrictions.
It is not an assumed object solving the desired square.

The definitions `quasiIsoOreInclusion f s hs` and `quasiIsoOreLift f s hs`
take the complete underlying strong maps of the constructed compatible
inclusion and lift. Write them as `a : S → A` and `g : S → B`.
`isQuasiIso_quasiIsoOreInclusion` proves that `a` is a full quasi-isomorphism.
The two `baseMap` lemmas identify their continuous maps exactly:

```text
a.baseMap = ContinuousMap.id A.presentation.space,
g.baseMap = hs.inverseBaseMap.comp f.baseMap.
```

`quasiIsoOre_square` proves the entire strong-map equality

```text
g ≫ s = a ≫ f.
```

Project the complete compatible square through `toStrongHom`. Compatible
composition and saturated composition are definitionally equal on these
full-domain-closed sources and intermediates, as recorded by the existing
`comp_eq_saturatedComp`. Thus the projected equality is precisely equality
for the actual category composition, including every bounded pullback.
It is not obtained merely by comparing continuous maps or spectrum points.

If `f` is also a full quasi-isomorphism,
`isQuasiIso_quasiIsoOreLift` proves the same for `g` by the existing compatible
Ore-lift theorem. This additional premise is not needed for square existence.

## Constructed fractions and both axioms

`quasiIsoOreRightFraction f s hs` is the actual Mathlib
`quasiIsomorphisms.RightFraction A B` with auxiliary source `S`, denominator
`a`, its proved full quasi-isomorphism, and numerator `g`.
`quasiIsoOreRightFraction_fac` records `a ≫ f = g ≫ s`.

The new `HasRightCalculusOfFractions` instance supplies Mathlib's two exact
conditions, extending the existing multiplicativity of `quasiIsomorphisms`:

- For a left fraction `φ`, take `f := φ.f` and `s := φ.s`. The constructed
  `quasiIsoOreRightFraction` and its complete square give the required right
  fraction and factorization. All objects already carry the closure
  hypotheses used by the geometric source-refinement construction.
- If `f₁ ≫ s = f₂ ≫ s` and `s` is a full quasi-isomorphism, the existing
  `cancel_saturatedComp` proves `f₁ = f₂` by bounded coefficient-test
  uniqueness and saturated-source extensionality. Choose the identity
  `t : X → X` as the required source refinement. It is already a full
  quasi-isomorphism, and the identity laws give `t ≫ f₁ = t ≫ f₂`.

The second condition is therefore proved with the identity refinement;
it is not a separate assumed cancellation or equalizer property.

## Remaining scope

This unit supplies the right calculus of fractions for the actual saturated
strong-map category and its specified full quasi-isomorphisms. It does not
yet give explicit representative or equality wrappers for the previously
constructed localization, identify that localization with an independently
defined analytic-space category, construct etale or equivariant sites, or
specialize to Harris towers. Those remain obligations of the surrounding
task.
