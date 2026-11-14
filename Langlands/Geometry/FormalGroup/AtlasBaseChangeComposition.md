# Successive coefficient extensions of actual formal atlases

## Setting and provenance

This is derived infrastructure for Drinfeld's convention that formal groups
include objects glued from formal groups over localizations: Drinfeld,
*Coverings of p-adic symmetric regions* (1976), printed p.109, paragraph
immediately before §2 (English translation, PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The comparison below is an internal consequence of actual coefficient extension
and the original atlas's transition cocycle. It does not add a representability
assumption.

Let `O` and `R` be commutative rings with `Algebra O R`, let `σ : Type` be finite,
and let `X : BasicAtlas O R σ`. For `S : CommAlgCat.{v} R` and
`T : CommAlgCat.{v} S`, it constructs an actual formal atlas isomorphism

```text
(X.baseChange S).baseChange T  ≅  X.baseChange (restrictTest S T).
```

Here `R : Type v`, all coefficient tests have universe `v`, and complete
compatible families have universe `v+1`. Covers may be infinite; coefficient
maps need no flatness or injectivity. The target `O`-algebra structures are the
structural composites, using `coefficientAlgebra` and `coefficientScalarTower`.
Their associativity in this construction is definitional. All declarations
below are in `Langlands.FormalGroup.ModuleLaw.BasicAtlas`.

## Covers, sources and chart comparisons

`baseCompOpens_eq` proves equality of the two sets of image generators by
`Set.image_image` and the composite structural map. This is an equality of
covers, and does not identify the independently chosen original sources.
`baseCompIterSource` selects an original chart through the two successive
preimage choices, transporting the image index across the equal covers.
`baseCompIter_unit` applies the existing unit-source property twice to show that
this original generator is invertible on every final coefficient test. The
direct source is `X.baseSource (restrictTest S T) b`, with its existing unit
certificate.

`baseCompLeftChartIso` composes the two identity-coordinate chart comparisons
from the successively extended chart to its selected original law on the final
restricted test. `baseCompChartIso` then applies the original atlas transition
from the iterated source to the direct source, followed by the inverse direct
chart comparison. `baseCompChartIso_coordinates` identifies its entire formal
coordinate series with that original transition. The two chosen sources may
differ even though their final generator images coincide, so this series need
not be the identity. `baseCompLeftTransition_coordinates` identifies the
successive atlas's transition series with the original transition at the
iterated source choices. The direct transition has the existing
`baseTransition_coordinates` formula.

## Actual formal maps and inverse equations

`baseCompHom` packages these chart maps as a formal atlas morphism. Coefficient
naturality follows from original transition naturality on the restricted test
map. The overlap square follows by two applications of the original cocycle:
both composites equal the original transition from the iterated source of the
first chart to the direct source of the second chart.

`baseCompInvChartIso` uses the reverse original transition between the two
sources. Its coordinate lemma retains that whole reverse formal series.
`baseCompInv` packages the reverse maps, with the reverse cover reindexing, and
proves the same naturality and overlap conditions. Finally `baseCompIso` uses
both actual formal maps. Each formal inverse equation follows from the original
transition cocycle and self-transition equation, before evaluation on points.
No detection of formal maps by point evaluation is used.

## Complete compatible families

For every `T`-algebra test `A` and every complete original family
`x : X.Point (restrictTest (restrictTest S T) A)`, `baseComp_onPoints` proves

```text
baseCompIso.onPoints
  ((X.baseChange S).toBaseChangePoints T
    (X.toBaseChangePoints S x))
  = X.toBaseChangePoints (restrictTest S T) x.
```

The equality includes every further coefficient-extension chart test. Its proof
uses the full-series coordinate lemma and the original family's transition
compatibility between its iterated-source and direct-source components.
`baseComp_inv_onPoints` proves the reverse square by the inverse linear
equivalence. Both sides use the actual complete compatible-family spaces,
including coefficient naturality and overlap compatibility.

This unit constructs the two-step formal comparison and its family squares.
Identity comparisons, coherence for three extensions, naturality in an arbitrary
atlas morphism, full acting-order compatibility, varying-base moduli class
functor laws, framing, heights and representability remain separate work.
