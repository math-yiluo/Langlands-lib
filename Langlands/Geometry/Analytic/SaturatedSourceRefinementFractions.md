# Source-subatlas normal forms for saturated localized morphisms

This is an internal construction from the existing complete reverse-map
identity, original-chart subatlases and right-fraction equality. It uses the
same actual saturated presentation localization as its predecessors and makes
no new original-literature attribution. Its provenance is the explicit
construction and deduction described below.

## Objects and assumptions

Let `K : Type u` be a complete ultrametric normed field. Ambient spaces have
universe `v`, and original chart indices have an independent universe `w`.
The objects `A` and `B` are actual `SaturatedAtlasPresentation` objects: each
contains an affinoid atlas presentation and a proof that its original chart
family contains every local full affinoid domain. Morphisms retain a continuous
ambient map and bounded algebra pullbacks for every admissible chart pair.
The quasi-isomorphism condition requires an ambient homeomorphism and the full
unique-factorization condition over all presented-affinoid test algebras.

Write `Q` for `localizationFunctor`. A right fraction from `A` to `B` has an
actual saturated source `S`, a full quasi-isomorphism `s : S ⟶ A`, and a strong
numerator `f : S ⟶ B`. Its interpretation is `Q(s)⁻¹ ≫ Q(f)` in the previously
constructed localization. These data and this interpretation are inherited
from `SaturatedLocalizedFractions`; no source or comparison equivalence is
assumed as an output premise.

## Actual same-space source subatlases

`IndexedAffinoidAtlas.RefiningSelection`, reused from `CommonSubatlas`, bundles
a set `P` of original indices, downward closure under containment of original
chart ranges, and the finite relative local refinement witnesses. It does
not contain an assumed net or output atlas.

`A.refiningSubpresentation P` wraps the existing constructed original-chart
subatlas as a saturated object. Its closure proof is
`subatlas_hasAllLocalDomains`: realize a selected chart's local full domain
as an original chart of `A`, then use containment in the selected parent chart
and downward closure to retain its index. The subatlas net is the one already
proved by the local refinement construction.

The new presentation has literally the same ambient space as `A`, and its
indices are the subtype of the original indices selected by `P`.
`refiningSubpresentation_space` records this definitional equality.
`A.refiningSubatlasInclusion P` is the existing full strong subatlas inclusion.
Its ambient map is the identity, and
`refiningSubatlasInclusion_pullback` computes every admissible pullback as the
original atlas restriction from the larger target chart to the selected source
chart. `isQuasiIso_refiningSubatlasInclusion` reuses the proved full
quasi-isomorphism condition for this inclusion. No directedness or upper
cofinality assumption is added.

## Constructing the source of a normalized fraction

For a right fraction `φ = (S, s, f)`, `fractionSourceSelection φ` retains those
original charts `j` of `A` such that

```text
range(chart_A j) ⊆ s.baseMap '' range(chart_S i)
```

for some original index `i` of `S`. `mem_fractionSourceSelection` is the exact
membership formula. Downward closure and local refinement are the existing
proved properties of `s`'s reverse-chart selection, using `A`'s full-domain
closure. Thus the selection supplies an actual original-chart subatlas of `A`.

Let `A_P` denote this constructed saturated subatlas.
`fractionSourceReverse φ : A_P ⟶ S` is the existing reverse compatible strong
map with its compatible wrapper forgotten. Every bounded pullback comes from
the earlier full affinoid-test reverse construction. Its ambient map is exactly
`s`'s inverse continuous map, by `fractionSourceReverse_baseMap`. Intrinsic
coherence of saturated maps supplies the coherence input used by that
construction.

`fractionSourceReverse_comp` proves the complete equation

```text
fractionSourceReverse φ ≫ s = A.refiningSubatlasInclusion P.
```

It projects the already proved compatible `reverse_comp` identity to complete
strong maps. This equation retains every admissible bounded algebra pullback;
it is not deduced from equality of spectrum points or only ambient maps.

## Normalization and its explicit common refinement

For any refining selection `P` and actual strong map `g : A_P ⟶ B`,
`sourceRefinementFraction P g` has the canonical inclusion `A_P ⟶ A` as its
denominator and `g` as its numerator. The denominator's full quasi-isomorphism
proof is constructed above, and its continuous map is literally the identity.

`sourceRefinedFraction φ` uses `fractionSourceSelection φ` and numerator
`fractionSourceReverse φ ≫ φ.f`. The exact numerator continuous map is
`φ.f.baseMap.comp φ.hs.inverseBaseMap`, as proved by
`sourceRefinedFraction_f_baseMap`.

`sourceRefinedFraction_commonRefinement` provides an explicit full common
refinement of the new and old fractions: the common source is the new subatlas,
the comparison map to the new source is its identity, and the comparison map
to the old source is `fractionSourceReverse φ`. The denominator equation is
`fractionSourceReverse_comp`; the numerator equation is the definition of the
new numerator. The common denominator is a full quasi-isomorphism because it
is the canonical inclusion. The relation requires this common denominator to
be a quasi-isomorphism; it does not separately require both comparison arrows
to be quasi-isomorphisms.

The exact right-fraction equality criterion now gives
`localizedRightFraction_sourceRefinedFraction`: the new and old fractions
interpret as the same localized arrow. The proof uses the explicit complete
common refinement, rather than assuming the normalization identity.

## Continuous map and representation of every arrow

`localizedSpaceFunctor_map_sourceRefinementFraction` says that the underlying
continuous map of `sourceRefinementFraction P g` is exactly `g.baseMap`.
The proof applies the descended space functor to the existing equation
`Q(inclusion) ≫ localizedRightFraction(...) = Q(g)`. Functoriality and the
original-arrow map formula identify the first factor with the identity
continuous map, so the TopCat identity law yields the result. This avoids any
claim that an ambient map determines all bounded pullbacks.

`exists_sourceRefinementFraction` proves that every localized arrow between
`Q(A)` and `Q(B)` has an actual pair `(P, g)` as above, simultaneously satisfying

```text
arrow = localizedRightFraction (sourceRefinementFraction P g)
localizedSpaceFunctor.map arrow = TopCat.ofHom g.baseMap.
```

The proof takes an existing arbitrary fraction representative, constructs its
reverse-chart source and numerator, then uses the proved normalization and
continuous-map identities. Existence is proved; the selection and numerator
are not asserted unique or canonical for the localized arrow.

## Scope

This unit constructs a source-subatlas normal form in the existing saturated
presentation localization. It does not identify that localization with a
separately defined analytic category or prove the full source-net Hom colimit
and injective transition-map assertions. Actual analytic etale, quasi-etale
and equivariant sites, compact/distinguished domains and Harris tower
specializations remain separate obligations of the surrounding task. All
predecessors retain their own independent acceptance and publication gates.
