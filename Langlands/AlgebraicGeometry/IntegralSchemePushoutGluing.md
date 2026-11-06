# Open saturated pieces of presheafed colimits

This is an internal construction for the global integral scheme pushout proof.
It derives its results from Mathlib's existing construction of colimits of
presheafed spaces; it does not formalize an additional assertion from the
Stacks Project. No scheme pushout existence assertion is proved in this file.

The indexing category `J` has independent object and morphism universes.
The presheaf value category `C` has object universe `u + 1` and morphism
universe `u`, while the underlying spaces have universe `u`. We assume
colimits of shape `J` in `TopCat` and limits of shape `Jᵒᵖ` in `C`.
These assumptions cover finite diagrams of presheafed spaces with values in
`CommRingCat.{u}`.

For diagrams `F`, `G` and a natural transformation `τ : F ⟶ G`, write
`q = colim.map τ`. The definition
`Langlands.AlgebraicGeometry.IntegralSchemePushout.PresheafedColimit.componentwiseMap`
constructs a natural transformation between the diagrams of sections of
`G` over an open `V` of its colimit and of `F` over the inverse image of
`V` under `q`. Its component is the section map of `τ.app j`, followed
by the presheaf's transport along the equality of inverse-image opens.
The equality `preimage_colimMap` follows from the colimit comparison equation.
Naturality follows from naturality of `τ`, naturality of its section maps,
and functoriality of restriction maps.

The lemma `colimMap_app_componentwiseMap` identifies `q.c.app (op V)`
with the map of these limits, using Mathlib's
`PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit`. Its proof compares
all limit projections and uses the colimit comparison equation for each
component. Consequently `isIso_colimMap_app` proves that this section map
is an isomorphism if every component section map over the inverse image
of `V` is an isomorphism.

Finally, `isOpenImmersion_colimMap` assumes that each component of `τ` is
an open immersion, that `q.base` is an open embedding, and the exact
saturation condition

```
range (τ.app j).base = (colimit.ι G j).base ⁻¹' range q.base.
```

It proves that `q` is an open immersion. For an open of the source colimit,
its image under the open embedding has inverse image in each component
contained in the range of that component's open immersion, by saturation.
The component section maps are therefore isomorphisms, and
`isIso_colimMap_app` gives the required colimit section isomorphism.
The open embedding and saturation hypotheses are explicit inputs; this
module does not construct or prove them for a pushout diagram.
