# Coefficient extension of actual principal-cover refinements

## Setting and provenance

This is derived infrastructure for Drinfeld's convention that formal groups
include objects glued from formal groups over localizations: Drinfeld,
*Coverings of p-adic symmetric regions* (1976), printed p.109, paragraph
immediately before §2 (English translation, PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The coefficient-extension comparison below is an internal consequence of the
actual localization atlases and their formal transitions.

Let `O` and `R` be commutative rings with `Algebra O R`, let `σ : Type` be
finite, and let `X : BasicAtlas O R σ`. A refinement `q : CoverRefinement X`
specifies a finer principal-generator set spanning the unit ideal, a selected
original chart for each finer generator, and an actual localization containment.
The cover need not be finite. For any `S : CommAlgCat.{v} R`, where `R : Type v`,
the construction gives a refinement of `X.baseChange S` and a formal isomorphism
between refining first and extending coefficients first. Tests are in universe
`v` and the complete compatible families are in universe `v+1`. Neither
flatness nor injectivity of `R → S` is assumed.

All declarations below are in
`Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement`.

## The extended refinement

`baseImageSource` chooses the image in `S` of the original source chart of the
chosen preimage of a finer generator. `baseImageSource_unit` proves the required
containment by applying the original refinement containment on the restricted
`R`-algebra `Localization.Away b`. Thus `baseChange` uses the image of the finer
generator set, the proved image-cover property, and these actual containments.

The two resulting finer atlases have the same generator set. They can select
different original source charts, since taking images in `S` can merge distinct
generators. `baseOriginalSource` records the source selected by extending the
original finer atlas; `baseSelectedSource` records the source selected by the
refinement of the extended original atlas. `baseOriginal_unit` and
`baseSelected_unit` show that both source generators are units on every relevant
restricted coefficient test.

## Actual formal comparison

`baseLeftChartIso` compares a chart of `q.atlas.baseChange S` with its original
source law on the restricted test. `baseRightChartIso` compares a chart of
`(q.baseChange S).atlas` with its selected original source law. Both are
composites of the existing identity-coordinate localization and coefficient
comparisons.

`baseChangeChartIso` goes through the original formal transition from
`baseOriginalSource` to `baseSelectedSource`, sandwiched between the left
comparison and the inverse right comparison. Its
`baseChangeChartIso_coordinates` equation identifies its full formal coordinate
series with that original transition series. This comparison can have
nonidentity coordinates. `baseLeftTransition_coordinates` and
`baseRightTransition_coordinates` identify the transitions of the two finer
atlases with original transitions at their respective source selections.

`baseChangeHom` packages the chart maps as an actual formal atlas morphism.
Naturality follows from original transition naturality on restricted coefficient
maps. Its formal transition square follows by applying the original cocycle
equation twice: both routes equal the transition from the first original source
to the second selected source. These are equalities of full formal series.

`baseChangeInvChartIso` uses the original transition in the reverse direction.
`baseChangeInvChartIso_coordinates` identifies its full series with that reverse
transition. The same naturality and cocycle argument constructs `baseChangeInv`.
Finally `baseChangeIso` supplies both actual formal maps, with both formal
inverse equations proved from the original transition cocycle and self-transition
equations. In particular the inverse equations are established before evaluation
on points.

## Complete compatible families

For every `S`-algebra test `A` and `x : X.Point (restrictTest S A)`,
`baseChange_onPoints` proves

```text
baseChangeIso.onPoints
  (q.atlas.toBaseChangePoints (q.onPoints x))
    = (q.baseChange S).onPoints (X.toBaseChangePoints x).
```

The equality holds on every coefficient-extension chart test. Its proof
evaluates the original transition series on the original-source component of
`x`, then applies `x`'s transition compatibility to obtain its selected-source
component. `baseChange_inv_onPoints` proves the reverse square using the inverse
of the constructed complete-family linear equivalence. The underlying point
spaces include all coefficient naturality and overlap compatibility conditions.

This unit supplies refinement base change and its actual formal comparison.
Full acting-order compatibility, base change of different-cover comparison
witnesses, varying-base moduli classes, framing, heights and representability
remain separate.
