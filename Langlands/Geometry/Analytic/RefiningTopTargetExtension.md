# Strong-map extension from a refining source subatlas

This module constructs a unique extension of an actual strong atlas map from a refining original source subatlas when the target has a greatest chart. It is an internal construction from bounded-map descent, actual target-domain factorization and complete bounded-map source separation. It makes no new assertion of correspondence with an original-literature statement.

The field `K : Type u` is a complete normed field with ultrametric distance. The source and target are actual `AffinoidAtlasPresentation.{u,v,w} K`, with independent field, space and chart-index universes. A source selection `P : A.atlas.RefiningSelection` is downward closed and locally refining in the original finite relative-neighborhood sense. The target index `t` is greatest by chart-image containment: every original target chart image is contained in its image. The input is a `StrongHom (A.refiningSubpresentation P) B`, including its continuous point map and every admissible bounded pullback. No nontrivial-valuation, reducedness, nonemptiness or source-saturation assumption is added.

## Descending the greatest-chart pullbacks

`selectedTopPullbacks` takes the input pullback from the greatest target chart to each selected source chart. The greatest-chart image condition follows from the input strong map's target-existence property. Its original-containment naturality equations follow from strong naturality with both target indices equal to `t`, followed by the actual target identity restriction. This produces exactly the `SelectedBoundedMapFamily` input of bounded-map descent.

`selectedTopPullbacks_extend_chart` proves that the descended bounded maps induce the unchanged continuous point map. Compactness supplies a finite cover of any parent chart by selected charts. Lift a point to one of these selected charts. The original source restriction's spectrum map returns the original point, by the parent chart's injectivity. Recovery of the descended bounded map on that selected chart identifies the two spectrum composites, by evaluation on every element of the target algebra. The input strong map's chart equation then gives the desired original point-map equation.

`extendTopChosen` uses this descended bounded map on every original source algebra and the constant target choice `t`. Its point map is literally the input point map. The preceding chart equation proves its chart compatibility; descended bounded-map naturality and the target identity restriction prove all its source restriction equations.

## Full strong extension and recovery

`extendTop` applies `StrongHom.ofTopChart` to `extendTopChosen`. That existing construction factors the greatest-chart pullback through each actual admissible target domain and proves all bounded restriction equations. Thus the output retains pullbacks for every admissible source-target pair, beyond the chosen greatest target chart. `extendTop_baseMap` records literal preservation of the continuous point map.

`extendTop_restrictSubatlasSource` proves equality with the entire original strong map after restriction to the selected source subatlas. For each selected source chart and every admissible target chart, compare the complete bounded maps after precomposition with the target restriction from the greatest chart. The actual target-domain factorization uniqueness theorem makes this comparison injective on bounded maps. The defining factorization equation for `ofTopChart`, selected-chart recovery of bounded descent and the original input map's target restriction equation prove equality. Strong-map extensionality then supplies the full equality. Equality of spectrum point maps alone is never used to identify bounded maps.

## Uniqueness and the explicit equivalence

`extendTop_unique` compares any strong map on the entire original source having the prescribed selected restriction with the constructed extension. The existing complete bounded-map separation theorem makes restriction to a locally refining selection injective, yielding equality of strong maps.

`refiningSourceTopHomEquiv` bundles source restriction and `extendTop` as an explicit equivalence between strong maps on the original source and strong maps on its refining subpresentation, with the same greatest-chart target. Uniqueness proves one inverse law and full selected restriction recovery proves the other. In particular, the extension does not depend on the finite source covers used by bounded descent.

This contribution concerns literal strong maps and a supplied greatest target chart. The fully faithful affinoid embedding into the source quotient, identification with the full analytic category, and etale/equivariant sites remain separate obligations.
