# The glued free-cover group of a diagonalizable atlas and its descent datum

All schemes lie in an arbitrary universe `u`. Let `A` be a
`DiagonalizableAtlas H` (module `DiagonalizableAtlasComparison`) for a group
scheme `H` over `S`. It has charts `f i : Z i ⟶ S`, finitely generated
character groups `Λ i` and trivializations `(f i)*H ≅ D_{Z i}(Λ i)`. This
module builds a group scheme `A.group` over `A.space = ∐ Z i`. On the chart
`Z i` this group is the split torus `D(F(Λ i))` of the free cover. The module
also builds a descent datum `A.datum` for `A.group` along
`A.projection : ∐ Z i ⟶ S`. Its transition maps are the lifted comparisons
`A.lift`.

## Conjugation helpers

- `dconj a b u` turns an isomorphism `u : D_V(Λ) ≅ D_V(Λ')` into an
  isomorphism `a*D_X(Λ) ≅ b*D_X(Λ')` for `a, b : V ⟶ X`, by conjugating with
  `diagonalizableBaseChangeIso`. `pullIso_dconj` says that it commutes with
  pullback, and `dconj_refl` and `dconj_trans` hold.
- `pullIso_symm`: `pullIso` of an inverse is the inverse of `pullIso`.

## The atlas scheme and the glued group

- `space = ∐ Z i`, `inclusion i = Sigma.ι`, `projection = Sigma.desc f`, with
  `inclusion_projection`. `inclusion_isIso` says that `Sigma.desc inclusion`
  is an isomorphism.
- `model i = D_{Z i}(F(Λ i))`, and `group` is Worker 736's
  `DisjointGroupGluing.group inclusion model` (module
  `Langlands.GroupScheme.Descent.DisjointGroupGluing`).
- `groupChart i : (inclusion i)*group ≅ (inclusion i)*D_space(F(Λ i))` is
  `DisjointGroupGluing.componentIso` followed by the inverse of
  `diagonalizableBaseChangeIso`. For a chart coordinate `x : V ⟶ Z i` of
  `a : V ⟶ space`, `coord i x a hx` is the restriction of `groupChart i`
  along `x`.

## Transitions on chart coordinates

- `chartValue i j x y a b hx hy l hxl hyl : a*group ≅ b*group` is defined for
  two points `a, b : V ⟶ space` with chart coordinates `x, y` lying over the
  same `l : V ⟶ S`. It is `coord i x a hx`, then `dconj a b (A.lift i j x y l …)`,
  then the inverse of `coord j y b hy`. The laws of `lift` give
  `chartValue_pull`, `chartValue_self` and `chartValue_trans`.
- A general map `a : T ⟶ space` need not factor through one chart. It is
  decomposed with the published `CoproductComponents` pieces
  `pullback a (Sigma.ι Z i)`, and isomorphisms on the pieces are assembled
  with `DisjointComponents.pullbackIsoAlong` (module
  `DisjointPullbackCoherence`). `coordinate_base` recovers `x ≫ f i = l` from
  a chart factorization. `chartToAtlas` assembles the transition from a chart
  coordinate to an arbitrary target `b` over the pieces of `b`. `transition a
  b k ha hb` assembles the transitions `chartToAtlas` over the pieces of `a`,
  for `a, b : T ⟶ space` with `a ≫ projection = k = b ≫ projection`.
- `chartToAtlas_on_chart` and `transition_on_charts`: after pullback to any
  pair of chart coordinates, the assembled transition is `chartValue`.
- `iso_ext_on_charts`, `hom_ext_on_charts` and `iso_ext_on_three_charts`: two
  isomorphisms or homomorphisms between base changes along maps into `space`
  agree if they agree after pullback to all pairs (or triples) of chart
  coordinates. These use `DisjointComponents.pullIso_ext_along` (and its
  `pullHom` version) twice.
- From these: `transition_self`, `transition_pull` (compatibility with
  pullback) and `transition_trans` (the cocycle identity
  `transition a c = transition a b ≪≫ transition b c`). Each is checked on
  chart coordinates with the laws of `chartValue`.

## The descent datum

- `overlap : OverlapIso projection group` is the transition between the two
  projections `fst, snd : space ×_S space ⟶ space`.
- `overlap_cocycle`: the three pulled-back overlaps on the triple overlap are
  transitions, by `transition_pull`, and `transition_trans` gives the cocycle
  identity.
- `datum : Datum projection group` packages `overlap` and `overlap_cocycle`.
- `overlap_on_charts`: every pullback of `overlap` to a pair of chart
  coordinates is the corresponding `chartValue`.

Provenance: internal. The transitions follow the pattern of the published
atlas constructions (for example `Reductive/AffinePinnedAtlasTransitions`),
which assemble transitions over coproduct components. The mathematical idea
of descending split tori glued from local character data is from Conrad,
*Reductive group schemes* (2014), proof of Proposition B.3.8.
