# Coefficient extension of order-linear formal atlas maps

This internal construction lifts actual formal atlas morphism base change to
maps commuting with every element of an acting order. It is derived from the
existing formal-coordinate, coefficient-extension and order-action APIs.

The source convention is Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), English translation, printed p.109 (PDF page 3), paragraph immediately
before section 2: formal groups include objects glued from formal groups over
localizations. Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The results below are internal consequences of this localization model, rather
than additional theorems asserted by the cited paragraph.

## Parameters and scope

Let `O` and `R` be arbitrary commutative rings with `Algebra O R`, and let `D`
be a possibly noncommutative ring with `Algebra O D`. The atlases have finite
coordinate types in `Type`, possibly infinite principal covers, and coefficient
tests in universe `v`. Their original sets of cover generators are equal.
`E` and `E'` are actual `D`-actions on these atlases. Coefficient extension
uses any `S : CommAlgCat.{v} R`; neither flatness nor injectivity is required.

## Formal construction

`testOrderChart_coordinates_eq` compares the action series after replacing a
chart index by an equal index. `baseSourceOrderChart_coordinates` combines
this with the coefficient-route identity for order actions and the equality
of the chosen original source indices. It therefore compares the actual
formal endomorphism series on the transported source chart.

`Hom.baseChange` has exactly the underlying formal atlas map constructed by
`BasicAtlas.Hom.baseChange`. Its additional proof applies formal-map
extensionality and uses the unchanged map series, the two action-coordinate
comparisons, and the original commutation equation for an arbitrary `d : D`.
It proves commutation of actual formal maps, including nonlinear terms.
`baseChange_val` records the underlying-map identity.

`Hom.baseChange_id` and `Hom.baseChange_comp` are equalities of actual
order-linear formal atlas maps. Subtype extensionality reduces them to the
corresponding already-proved formal base-change laws.

## Complete compatible families and isomorphisms

`Hom.baseChange_onPoints` states, for every coefficient test `A` over `S`
and every original complete compatible family `x`, that

```text
(baseChange f) (toBaseChangePoints E x)
  = toBaseChangePoints E' (f x).
```

All three maps are linear for the full acting ring `D`. This square follows
from the underlying formal-map square because the order-linear maps use
exactly the same complete families and evaluation formulas.
`Hom.baseChange_fromPoints` states the reverse square using the inverse of
each constructed order-linear family equivalence. It likewise reduces to the
existing inverse complete-family square.

`Iso.baseChange` extends both actual order-linear formal maps. Formal
composition and identity preservation transport their inverse equations.
`Iso.baseChange_onPoints` and `Iso.baseChange_fromPoints` specialize the two
squares to the induced `D`-linear equivalences.

This unit does not construct base change for different-cover refinements or
comparisons, a varying-base quotient moduli functor, framing, heights or
representability.
