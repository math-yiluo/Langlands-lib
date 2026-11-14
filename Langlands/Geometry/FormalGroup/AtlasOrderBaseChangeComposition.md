# Successive coefficient extensions with the full acting order

## Setting and provenance

This is derived infrastructure for the actual localization-glued formal modules
of Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(English translation, PDF page 3): the paragraph immediately before §2 and the
formal order-module definition in §2 A. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The construction below lifts the internal two-step coefficient comparison to the
whole acting order, using the original order-linear formal transitions.

Let `O` and `R` be commutative rings with `Algebra O R`, let `D` be an arbitrary
possibly noncommutative ring with `Algebra O D`, let `σ : Type` be finite, and
let `E : OrderAction D X` for `X : BasicAtlas O R σ`. The coefficient objects are
`S : CommAlgCat.{v} R` and `T : CommAlgCat.{v} S`. The construction gives

```text
(E.baseChange S).baseChange T  ≅  E.baseChange (restrictTest S T)
```

by actual order-linear formal atlas maps on the equal image covers proved in
`AtlasBaseChangeComposition`. Here `R : Type v`, coefficient tests have universe
`v`, and complete compatible families have universe `v+1`. Covers may be
infinite. Coefficient maps require no flatness or injectivity. The structural
composite `O`-algebra instances and scalar towers are the same as in that
underlying construction. All declarations below are in
`Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction`.

## Formal order compatibility

`baseCompLeftOrderChart_coordinates` applies the existing coefficient-action
coordinate formula twice. It identifies the action series on a successive chart
with the original action series at `X.baseCompIterSource S T b`, on the final
restricted coefficient test. The direct action uses its existing
`baseOrderChart_coordinates` formula at `X.baseSource (restrictTest S T) b`.
The original source charts may be different.

`baseCompHom` has underlying formal map exactly `X.baseCompHom S T`. For each
`d : D`, its commutation equation reduces, using the action-coordinate formulas
and the full-series formula for `X.baseCompChartIso`, to `E.transition` between
the iterated and direct original sources. That original transition commutes
with every order element. The proof is an equality of actual formal coordinate
series. It adds full `D`-compatibility to the already constructed coefficient
naturality and overlap equations.

`baseCompInv` retains exactly `X.baseCompInv S T`. It uses the reverse cover
reindexing and the reverse original transition, and proves order commutation by
the corresponding original `E.transition` equation in that direction.
`baseCompHom_val` and `baseCompInv_val` state that forgetting order commutation
retains these exact underlying formal maps, by reflexivity.

`baseCompIso` packages both order-linear maps. Its two formal inverse equations
are obtained by subtype extensionality from `X.baseCompIso`'s formal inverse
laws. Thus they hold as formal maps before evaluation on points.

## Complete compatible families

For every final `T`-algebra test `A` and every
`x : E.Point (restrictTest (restrictTest S T) A)`, `baseComp_onPoints` proves

```text
baseCompIso.onPoints
  ((E.baseChange S).toBaseChangePoints T
    (E.toBaseChangePoints S x))
  = E.toBaseChangePoints (restrictTest S T) x.
```

This uses the previously proved underlying complete-family equation, since
both order-linear maps retain those exact functions. The displayed maps and
equivalences are linear over all of `D`. `baseComp_inv_onPoints` gives the
reverse square using the actual inverse equivalence and the underlying reverse
family equation. The point spaces include coefficient naturality and overlap
compatibility on every further coefficient-extension chart test.

This unit is the full-order lift of the two-step comparison. Identity and
three-step coherence, naturality in arbitrary formal atlas maps, varying-base
special or height-certified moduli class functor laws, framing and
representability remain separate obligations. No height or specialness
certificate is inferred here.
