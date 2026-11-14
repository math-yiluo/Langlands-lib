# Order-linear refinement and coefficient-extension compatibility

## Setting and provenance

This is derived infrastructure for Drinfeld's localization-gluing convention:
Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109,
paragraph immediately before §2 (English translation, PDF page 3). The
registered source is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The formal comparison comes from `AtlasRefinementBaseChange`; the present
internal derivation proves that it retains the full acting-order structure.

Let `O` and `R` be commutative rings with `Algebra O R`, let `D` be a possibly
noncommutative ring with `Algebra O D`, let `σ : Type` be finite, and let
`E : OrderAction D X` on an actual formal `O`-module atlas
`X : BasicAtlas O R σ`. Let `q : CoverRefinement X` be an actual principal-cover
refinement. For any `S : CommAlgCat.{v} R`, the two orders of restriction and
coefficient extension give the order actions
`(q.orderAction E).baseChange S` and
`(q.baseChange S).orderAction (E.baseChange S)`.
Their underlying atlases have equal finer generator sets, but may select
different original source charts. Covers can be infinite and neither flatness
nor injectivity of `R → S` is assumed. Tests have universe `v`, the universe of
`R`; complete compatible families have universe `v+1`.

All declarations below are in
`Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement`.

## Formal order compatibility

`baseLeftOrderChart_coordinates` identifies the full order-endomorphism series
of the extended finer action with the original action at
`baseOriginalSource`. It composes the coefficient-extension coordinate identity
with the original refinement coefficient identity.
`baseRightOrderChart_coordinates` identifies the refined extended action with
the original action at `baseSelectedSource`, by composing those identities in
the opposite order.

`orderBaseChangeHom` retains exactly `baseChangeHom` as its underlying actual
formal atlas map. For every coefficient test, chart and `d : D`, its commutation
equation is an equality of formal module homomorphisms. Coordinate
extensionality reduces this to the original `E.transition` commutation equation
between the two source selections, using the two action-series identities and
the full series formula for `baseChangeChartIso`.
`orderBaseChangeInv` proves the same equation for the exact underlying
`baseChangeInv`, using the original transition in the reverse direction.
`orderBaseChangeHom_val` and `orderBaseChangeInv_val` record the definitional
identities of the underlying formal maps.

`orderBaseChangeIso` packages these two order-linear formal maps. Subtype
extensionality transports both formal inverse equations from `baseChangeIso`.
Thus both order compatibility and inverse equations hold for full formal maps,
including all nonlinear coefficients.

## Complete compatible families

The constructed `orderBaseChangeIso.onPoints` is a `D`-linear equivalence on the
complete compatible-family point spaces. `orderBaseChange_onPoints` proves,
for every `S`-test `A` and `x : E.Point (restrictTest S A)`,

```text
orderBaseChangeIso.onPoints
  ((q.orderAction E).toBaseChangePoints (q.orderOnPoints E x))
    = (q.baseChange S).orderOnPoints (E.baseChange S)
        (E.toBaseChangePoints x).
```

The reverse square is `orderBaseChange_inv_onPoints`, using the inverse
`D`-linear equivalence. Both identities reuse the underlying complete-family
squares because these order-linear maps have exactly those underlying
functions. In particular these are equalities of families on all
coefficient-extension chart tests.

This unit supplies full-order refinement compatibility. Base change of
different-cover comparison witnesses, varying-base moduli classes, framing,
heights and representability remain separate.
