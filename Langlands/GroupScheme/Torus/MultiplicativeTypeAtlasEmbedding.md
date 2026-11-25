# The descended torus of a diagonalizable atlas and the embedding into it

All schemes lie in an arbitrary universe `u`. Let `A` be a
`DiagonalizableAtlas H` for a group scheme `H` over `S`, with glued group
`A.group` over `A.space = ∐ Z i` and descent datum `A.datum` (module
`MultiplicativeTypeAtlas`). This module does four things:

- it builds a closed embedding `A.embedding : P*H ⟶ A.group` over `A.space`,
  where `P = A.projection`;
- it proves that the embedding is compatible with the canonical datum of `H`
  and with `A.datum`;
- it descends `A.group` to a group `A.torus` over `S`, and the embedding to
  `A.torusEmbedding : H ⟶ A.torus`, assuming `P` is fppf;
- it proves that `A.torusEmbedding` is a closed immersion and that `A.torus`
  is a split torus over every chart.

## Base-change bookkeeping

- `baseChange_map_diagonalizableBaseChangeIso`: the comparisons
  `diagonalizableBaseChangeIso` are compatible with iterated base change along
  `a : V ⟶ X` and `P : X ⟶ S` with `a ≫ P = l`. This is an instance of
  `pullbackComparison_tower'`, since all maps to `Spec ℤ` agree.
- `pullHom_canonicalOverlap`: pulling back the canonical overlap of `p*C` to a
  test scheme with coordinates `a, b` (over the same `l`) gives
  `pullbackComparison … a … ≫ (pullbackComparison … b …)⁻¹`.

## The embedding over the atlas scheme

- `pulled = P*H`. `pulledChart i` identifies `(inclusion i)*P*H` with
  `(inclusion i)*P*D_S(Λ i)` through `A.triv i` and `pullbackComparison`.
- `coverMap i : P*D_S(Λ i) ⟶ D_space(F(Λ i))` is
  `diagonalizableBaseChangeIso` followed by `D(proj (Λ i))`.
- `embeddingComponent i` is `pulledChart i`, then the base change of
  `coverMap i`, then the inverse of `groupChart i`. `embedding` assembles
  these with the published `DisjointComponents.groupHom`, and
  `baseChange_map_embedding` recovers each component.
- `embedding_on_chart`: for a chart coordinate `x : V ⟶ Z i` of
  `a : V ⟶ space` over `l : V ⟶ S`, the base change of `embedding` along `a`
  is `chartTriv i x l`, then `D_V(proj (Λ i))`, then `coord i x a` back. This
  is computed with `pullHom` calculus and the bookkeeping lemmas above. It
  uses `baseChange_map_diagonalizableMap` (module `RelativeDiagonalizableHomLocality`).
- `embedding_compatible`:
  `Compatible (canonicalDatum P H) A.datum A.embedding`. By
  `hom_ext_on_charts` it suffices to check this on pairs of chart coordinates
  `x, y` over the same point. There the overlap of `A.datum` is `chartValue`
  (`overlap_on_charts`), the canonical overlap is given by
  `pullHom_canonicalOverlap`, and the embedding is given by
  `embedding_on_chart`. The remaining identity is `lift_comm`:
  `comparison ≫ D(proj) = D(proj) ≫ lift`.

## Closedness

- `isClosedSubgroup_of_inclusions`: a homomorphism of group schemes over
  `space` is a closed immersion if its base change to every chart is. Closed
  immersions are Zariski-local on the target, and the charts form Mathlib's
  open cover `sigmaOpenCover`. The base change to a chart is the pullback
  along that open (`baseChange_map_isPullback`).
- `isClosedSubgroup_embeddingComponent`: `D(proj)` is a closed immersion
  (`isClosedSubgroup_diagonalizableMap_proj`, because `proj` is surjective). So
  is its base change, and composing with isomorphisms keeps it one.
- `isClosedSubgroup_embedding` combines these.

## Descent to the base

- `group_isAffineHom`: `A.group` has affine structure map. Each model
  `D(F(Λ i))` is affine over its chart (`Diagonalizable.isAffineHom`, stable
  under base change), and the `DisjointGroupGluing` instance passes
  affineness to the glued group.
- From now on assume `P` is flat, locally of finite presentation and
  surjective. `torus` is the group `A.datum.fppfSolution.obj` of
  `Datum.fppfSolution` (module `FppfEffectivity`).
- `torusEmbedding : H ⟶ torus` is `Solution.descendHomOfFppf` of `embedding`
  from the canonical solution of `H` to `A.datum.fppfSolution`, using
  `embedding_compatible` (module `FppfHomDescent`).
- `baseChange_map_torusEmbedding`:
  `P*torusEmbedding = embedding ≫ fppfSolution.iso.inv`, from
  `baseChange_descendHomOfFppf`.
- `isClosedSubgroup_torusEmbedding`: the base change of `torusEmbedding` along
  `P` is a closed immersion followed by an isomorphism.
  `IsClosedSubgroup.of_baseChange_of_fppf` (module `FppfReflection`) descends
  this.
- `isSplitTorus_baseChange_torus i`: `(f i)*torus` is a split torus. Through
  `pullbackComparison` along `f i = inclusion i ≫ P`, the solution
  isomorphism and `DisjointGroupGluing.componentIso`, it is isomorphic to
  `D_{Z i}(F(Λ i))`. That group is a split torus because `F(Λ i)` is finite
  free (`isSplitTorus_diagonalizable_cover`).

Provenance: internal. This implements Conrad, *Reductive group schemes*
(2014), proof of Proposition B.3.8: embed each diagonalizable piece in a split
torus, glue, and descend. The detailed construction is part of this
formalization.
