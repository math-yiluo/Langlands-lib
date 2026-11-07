# Compatible open subdiagrams of colimits

This internal construction supports the global integral scheme pushout proof. It
uses Mathlib's universal properties for colimits of types and topological spaces.
It does not assert scheme pushout existence, and does not require algebraic or
sheaf hypotheses.

The indexing category has independent object and morphism universes. Both
diagrams take values in a single universe of types or topological spaces. The
results use arbitrary supplied colimit cocones, so their types do not require a
chosen colimit or any extra size condition on the indexing category.

## Colimits of types

For a natural transformation `τ : F ⟶ G` and a cocone `cF` on `F`,
`TypeColimit.partialSection` assigns `some (cF.ι_j x)` to a point in the range
of `τ_j`, choosing a preimage `x`, and assigns `none` otherwise. Componentwise
injectivity makes its value at `τ_j x` equal to `some (cF.ι_j x)`.

`TypeColimit.injective_and_range` assumes both supplied cocones are colimits,
a comparison `q` commuting with all legs, injectivity of every `τ_j`, and the
cartesian range condition

`G.map f ⁻¹' range τ_k = range τ_j`

for every arrow `f : j ⟶ k`. The partial sections then form a cocone on `G`.
Its descended map `r` satisfies `r (q x) = some x`. This proves injectivity of
`q`. Applying `r` also proves the saturation identities

`range τ_j = cG.ι_j ⁻¹' range q`.

This argument includes empty components and an empty indexing category: it
uses joint surjectivity of a type-colimit cocone only for an existing point.

## Colimits of topological spaces

`TopologicalColimit.isOpenEmbedding_of_injective_of_range` assumes that the
large cocone is a colimit, `q` is injective and commutes with all legs, each
`τ_j` is an open embedding, and the displayed saturation identities hold.
For an open set `S` in the small cocone point, the inverse image of `q(S)`
under the large leg at `j` is the image under `τ_j` of the inverse image of `S`
under the small leg. This is open. The final topology of the large colimit
therefore makes `q` an open map, and continuity and injectivity give an open
embedding. The small cocone need not be a colimit for this intermediate result.

`TopologicalColimit.isOpenEmbedding_of_cartesian` applies the type-colimit
argument after forgetting topology, using Mathlib's preservation of colimits
by `TopCat`'s forgetful functor. Thus a comparison between two supplied
colimits is an open embedding, with the saturation identities, whenever its
components are open embeddings and the cartesian range condition holds.

These are internal consequences of the cited Mathlib APIs. They do not claim
that a particular scheme diagram has compatible affine charts, or that a
colimit of locally ringed spaces is a scheme.
