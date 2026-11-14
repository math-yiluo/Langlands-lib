# Coefficient extension of actual formal atlas morphisms

## Setting and provenance

This is derived infrastructure for Drinfeld's convention that formal groups
may be glued from formal groups over localizations: Drinfeld, *Coverings of
p-adic symmetric regions* (1976), printed p.109, paragraph immediately before
§2 (English translation, PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The constructions here are internal consequences of the actual atlas and
coefficient-extension definitions, rather than an additional theorem ascribed
to that paragraph.

Let `O` and `R` be commutative rings with an `O`-algebra structure on `R`.
The source and target are actual formal `O`-module atlases with finite
coordinate types, possibly different. Their principal-generator sets are
equal, as specified by `h`. Covers can be infinite. Coefficient tests have
universe `v`, the universe of `R`; compatible families have universe `v+1`.
For any commutative `R`-algebra `S` in the same universe, the new covers are
the images of the original generator sets in `S`. Neither flatness nor
injectivity of `R → S` is required.

## Actual formal construction

All declarations below are in
`Langlands.FormalGroup.ModuleLaw.BasicAtlas`.

- `baseOpens_eq` identifies the two image covers.
- `baseSource_sourceChart` proves that the chosen original generator for a
  transported image chart agrees with the transported chosen original
  generator. The preimage choice depends on the generator set and its image
  predicate, so equality of the sets suffices even if distinct generators
  acquire equal images.
- `testChart_eq`, `testTransition_coordinates_eq` and `family_chart_eq`
  transport laws, transition series and family tuples along equal chart
  indices. Their proofs eliminate the supplied index equalities.
- `baseSourceChartIso` compares the extended source law on a test with its
  original source law, indexed using the target's chosen generator. Its
  coordinates and inverse coordinates are identity series. Equality of the
  addition and action series follows from composition of coefficient maps
  and `testChart_eq`.
- `baseSourceTransition_coordinates` identifies the corresponding source
  transition series, using the original index equalities.

`Hom.baseChartHom` conjugates the original formal map on the restricted
`R`-test by `baseSourceChartIso` and the inverse target `baseChartIso`.
`Hom.baseChange` packages these maps as an actual atlas morphism over `S`.
They are formal `O`-linear maps in every chart, natural in the coefficient
algebra and commuting with the actual formal transition maps.

`Hom.baseChartHom_coordinates` and `Hom.baseChange_coordinates` say that the
extended map has precisely the original map's coordinate series on the
restricted test and chosen original target chart. The comparison maps have
identity coordinates, so the conjugation simplifies by the two identity
substitution laws. Original coefficient naturality then proves new
naturality. The original formal transition square, together with the source
and target transition-series comparisons, proves the new formal transition
square.

`Hom.baseChange_id` and `Hom.baseChange_comp` prove preservation of identity
and composition as equalities of actual atlas morphisms. Coordinate
extensionality reduces these identities to identity substitution and the
chosen-source equality. Composition uses the convention that the right map
is applied first.

## Full compatible families and isomorphisms

For every `S`-test `A` and original compatible family `x`,
`Hom.baseChange_onPoints` proves

```text
(baseChange f).onPoints (toBaseChangePoints x)
  = toBaseChangePoints (f.onPoints x).
```

This equality holds on every coefficient-extension chart test, not merely
on tuples on the base cover. Its proof compares the actual formal coordinate
series and the original family components at equal source indices.
`Hom.baseChange_fromPoints` proves the corresponding square for the
constructed inverse family comparison, using injectivity and the two inverse
laws of `baseChangePointEquiv`.

`Iso.baseChange` extends both formal maps of an actual same-cover
isomorphism. Preservation of composition and identity transports its two
formal inverse equations. `Iso.baseChange_onPoints` gives the same square
with the full-family linear equivalences.

This unit extends maps between equal-cover atlases. Base change of arbitrary
refinements and of comparisons between different covers remains separate.
It supplies no varying-base quotient functor, order-linearity, height,
framing, moduli triple or representability assertion.
