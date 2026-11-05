# Complete strong restriction and equality on a common source subatlas

This is an internal construction from original-chart restrictions, full
quasi-isomorphism cancellation, source-subatlas normalization and the existing
right-fraction equality criterion. It makes no new original-literature
attribution. The construction and proof below give its provenance.

## Objects and assumptions

Let `K : Type u` be a complete ultrametric normed field. The actual saturated
atlas presentations `A` and `B` have ambient universe `v` and original-index
universe `w`, independently. Their morphisms retain a continuous ambient map
and a bounded algebra pullback at every admissible chart pair. Saturation
means that the original chart family contains every local full affinoid
domain. Full quasi-isomorphisms require an ambient homeomorphism and the
unique-factorization property over all presented-affinoid test algebras.

A `RefiningSelection` is a set of original atlas indices with downward closure
under chart-range containment and the proved finite relative local-refinement
condition. For a selection `P`, write `A_P` for the constructed saturated
`A.refiningSubpresentation P` and `i_P` for its canonical full
quasi-isomorphism inclusion in `A`. Its ambient space is literally that of
`A`. These are the existing constructions from
`SaturatedSourceRefinementFractions`, rather than assumed output atlases.

## Complete strong maps between selections

For `h : P ≤ Q`, `A.refiningSubatlasMap h : A_P ⟶ A_Q` has identity ambient
map. The chosen target chart for a selected index `i` is the same original
index, now with its membership in `Q` proved by `h`. Every admissible
pullback from a target chart `j` to the source chart `i` is exactly

```text
A.presentation.atlas.restriction i.val j.val containment.
```

`refiningSubatlasMap_baseMap` and `refiningSubatlasMap_pullback` record these
exact formulas. The chart equation is the original restriction chart equation.
Compatibility with restrictions follows by applying `restriction_comp` to
the two paths through a nested source and target chart. This constructs a
complete strong map, including all bounded pullbacks.

`isQuasiIso_refiningSubatlasMap` proves the full quasi-isomorphism condition:
the identity ambient map is a homeomorphism, and each original atlas
restriction has the required full domain universal property by
`restriction_represents`. The represented locus is the preimage under the
target chart of the identity image of the source chart range.

`refiningSubatlasMap_inclusion` proves the inclusion diamond

```text
refiningSubatlasMap h ≫ i_Q = i_P.
```

This is equality of complete strong maps. Saturated strong-map
extensionality reduces it to one admissible target chart for each source
chart. Choose the same original index, first in `Q` and then in `A`.
The exact saturated-composition pullback formula computes the composite
through that chart; the original atlas's `restriction_comp` identifies the
result with the direct restriction. This proof does not infer equality of
bounded maps from equality of spectrum points.

`refiningSubatlasMap_id` and `refiningSubatlasMap_comp` prove identity and
composition by postcomposing with the canonical inclusion in `A`. The
inclusion diamond makes those composites equal, and the existing
`postcompQuasiIsoEmbedding` cancels the full quasi-isomorphism inclusion.
Thus `refiningSubatlasFunctor A` realizes the inclusion order of selections
in the actual full saturated strong-map category.

## Restricting actual numerators

For `h : P ≤ Q` and `f : A_Q ⟶ B`, `refiningHomRestriction h f` is the
complete composite `refiningSubatlasMap h ≫ f`. Its identity and iterated
restriction laws are `refiningHomRestriction_id` and
`refiningHomRestriction_comp`, using the proved map laws and associativity.
There is no assertion here that these restriction functions are injective.

`HasCommonSourceRefinement f g : Prop`, for `f : A_P ⟶ B` and
`g : A_Q ⟶ B`, means that there is a refining selection `R` with
`R ≤ P` and `R ≤ Q` such that the two complete restrictions to `A_R` are
equal. Both the witness and its comparison maps use original source-object
charts; the witness is not an arbitrary supplied comparison category.

## Exact equality criterion

`localizedSourceRefinement_eq_iff` proves

```text
localizedRightFraction (sourceRefinementFraction P f)
  = localizedRightFraction (sourceRefinementFraction Q g)
    ↔ HasCommonSourceRefinement f g.
```

The equality on the left is in the already constructed saturated presentation
localization. The equality in the predicate on the right compares the entire
strong maps, with all admissible bounded algebra pullbacks.

For the forward implication, the existing arbitrary-fraction criterion
provides a saturated source `S`, complete maps `a : S ⟶ A_P` and
`b : S ⟶ A_Q`, and full equations

```text
a ≫ i_P = b ≫ i_Q
a ≫ f = b ≫ g.
```

Their common denominator `t = a ≫ i_P` is a full quasi-isomorphism.
Apply source-subatlas normalization to the fraction from `A` to `S` with
denominator `t` and numerator the identity of `S`. This constructs a refining
selection `T` of original `A` charts and a complete reverse map
`r : A_T ⟶ S` with `r ≫ t = i_T`.

Take `R = (T ⊓ P) ⊓ Q`; the existing intersection semilattice gives the
three containments, and its refining-selection structure supplies an actual
source subatlas. Put `c = refiningSubatlasMap (R ≤ T) ≫ r`.
The reverse identity and inclusion diamond give `c ≫ t = i_R`.
Postcomposing `c ≫ a` and the canonical `A_R ⟶ A_P` with `i_P` gives equal
maps to `A`, so full quasi-isomorphism cancellation identifies them. The
denominator equation gives the corresponding identity for `c ≫ b` and
the canonical `A_R ⟶ A_Q`. Precomposing the old numerator equation with
`c` now proves equality of the two actual restrictions on `A_R`.

For the reverse implication, use `A_R` as the arbitrary-fraction common
source and the two constructed selection maps as its comparison maps.
The inclusion diamonds identify both composite denominators with `i_R`,
which is a full quasi-isomorphism. The assumed complete restriction equality
is exactly the numerator equation. The existing fraction equality criterion
therefore gives equality of the two localized arrows.

## Scope

This unit constructs complete strong restriction along nested selections and
proves exact equality of source-subatlas fraction representatives. It does
not yet assemble their Hom quotient, prove its colimit universal property,
or prove injectivity of restriction transitions. It makes no claim that
continuous ambient maps determine bounded pullbacks. Identification with a
separately defined analytic category, actual analytic etale, quasi-etale and
equivariant sites, compact/distinguished domains and Harris tower
specializations remain obligations of the surrounding task. Every
predecessor retains its independent acceptance and publication gate.
