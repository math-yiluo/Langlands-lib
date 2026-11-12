# Points under a change of relative base

This is an internal construction from the published definitions of presheaf
points, restriction, represented products, and the atlas quotient topology. It
supplies a comparison between point spaces whose presheaves live over different
base schemes. It is supporting content for geometric component transport.

Let `g : T ⟶ S` and let `F` be a presheaf on schemes over `S`.
`RestrictionPoints.equiv` constructs an equivalence

```
Points ((restrictPresheaf g).obj F) ≃
  Points (F ⨯ (schemeYoneda S).obj (Over.mk g)).
```

There are no atlas or sheaf assumptions for this equivalence of sets.
`sectionPair` constructs a section of a presheaf product using the Yoneda
equivalence and the categorical product lift. Its projection, extensionality,
and pullback lemmas avoid any dependence on a particular model of the product.

`toProduct` keeps the field and the section of a field point over `T`, composes
its structure morphism with `g`, and records the original structure morphism
as the represented factor. `productStructure` extracts that factor in the
reverse direction. `fromProduct` uses it as the structure morphism to `T`;
an identity scheme map over `S` transports the first factor to the required
test object. Both constructions preserve the relation of agreeing over a
common field extension. Their composites are related to the identity, using
identity field embeddings, so they descend to inverse maps on quotient points.

For a scheme chart `a : h_U ⟶ F`, `chartIso` identifies the scheme underlying
the restricted chart with the scheme underlying the product chart. It is the
inverse of `Over.prodLeftIsoPullback U (Over.mk g)`, regarded over `S`.
Its two projection identities identify the actual scheme maps to `U` and
`T`. `toProduct_restrictAtlas` proves compatibility on field-valued chart
points. `equiv_chartPointMap` passes to ordinary scheme points using their
residue fields and `schemePoint_schemeValue`; the inverse chart identity
follows by applying the point equivalence.

If `a` is étale and geometrically surjective, `RestrictionPoints.homeomorph`
upgrades the equivalence to a homeomorphism for the two actual `pointTopology`
structures. The restricted and product charts retain both properties.
Each is a quotient map on points by `isQuotientMap_chartPointMap`.
The chart identities therefore reduce continuity of each direction to
continuity of the other chart composed with the corresponding scheme
isomorphism.

`baseChangePointsHomeomorph g X` specializes this construction to any algebraic
space `X` over `S`, choosing its existing étale surjective atlas. It identifies
the actual point topology of `(baseChange g X).presheaf` with that of
`X.presheaf ⨯ h_T` over `S`. No quasi-separatedness, finite presentation,
Noetherian, or field hypothesis is needed.

This comparison does not by itself assert constancy or constructibility of
geometric component counts. Field-extension invariance and the remaining
generic descent and approximation arguments are separate obligations.
