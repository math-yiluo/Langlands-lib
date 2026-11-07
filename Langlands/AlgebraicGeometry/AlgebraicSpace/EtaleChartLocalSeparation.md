# Local separatedness and the étale-chart topology

Author: Worker 105.

This proof module proves the two properties of Proposition 5.4 of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed pp.14–16 (source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`) that need the target
to be locally separated: étale morphisms give local homeomorphisms, and fibre products
are compatible. These are exactly the two properties that fail without local
separatedness (see the section "Correction" of the Markdown of
`HenselianSpacePointTopologyStatement`). Local separatedness (`IsLocallySeparated`) is the
Stacks Project's: the diagonal is a representable immersion (source
`stacks-algebraic-spaces-chapter-ed88ff78-2026-11-05`, SHA-256
`49a75fa582cbeafadb9e1fbbdce130e5b8971322a2c0048d777e8a97f0d0fcf5`, Definition 13.2,
Tag 02X5(2)). The module builds on `EtaleChartTopologyFunctorial`.

## Scheme lemmas

- `isOpenImmersion_of_section`: a section `s` of an étale morphism `f` of schemes is an
  open immersion. Mathlib's `pullback_lift_diagonal_isPullback` exhibits the graph
  `Y → Y ×_{X} X` of `s` (fibre product over `s ≫ f = 𝟙`) as a base change of the
  diagonal of `f`. That diagonal is an open immersion for formally unramified maps locally
  of finite type (`isOpenImmersion_diagonal`). Then `s` is the graph followed by the
  second projection, an isomorphism.
- `isEmbedding_schemePointMap_of_isImmersion`: an immersion of schemes over `Spec K`
  induces an embedding on rational points. Mathlib factors an immersion as the closed
  immersion `liftCoborder` into the open subscheme `coborderRange`, followed by its open
  immersion. The two pieces give embeddings on points by
  `isEmbedding_schemeClosedPointMap` and `isOpenEmbedding_schemePointMap`.

## Overlaps embed into products

Let `X` be locally separated and `a : h_U → X`, `b : h_V → X` maps from schemes. The
product `U ⊗ V` is the fibre product over `Spec K`.

- `pairPullbackLift_mem_of_relative_diag`: if the diagonal of `X` is representable with
  projections in a property `P` of monomorphisms respecting isomorphisms, then the pairing
  `U ×_X V → U ⊗ V` of the two projections is in `P`. `isImmersion_pairPullbackLift`
  (locally separated `X`) and `isClosedImmersion_pairPullbackLift` (separated `X`) are
  the two cases used.
  Proof: the Library's `exists_representsEqualizer_of_relative_diag`
  (`DiagonalEqualizer.lean`) applies to the relative property of the diagonal. For the two
  points `a ∘ pr₁` and `b ∘ pr₂` of `X` over `U ⊗ V` it gives `ι : Z → U ⊗ V` in `P`
  cutting out the locus where they agree. The universal properties give
  `φ : U ×_X V → Z` with `φ ≫ ι` equal to the pairing, and `ψ : Z → U ×_X V`. These are
  mutually inverse, using that `ι` is a monomorphism and that maps into the pullback are
  determined by their projections. So the pairing is an isomorphism followed by a member
  of `P`.
- `locallyOfFiniteType_pairPullback_of_isLocallySeparated`: if `U` and `V` are locally of
  finite type, so is `U ×_X V`. An immersion is locally of finite type, and so is
  `U ⊗ V → Spec K`.
- `isEmbedding_pairPullback_points`: the map
  `(U ×_X V)(K) → U(K) × V(K)`, `w ↦ (pr₁ w, pr₂ w)`, is a topological embedding. It is
  the embedding of the immersion above followed by the Library's homeomorphism
  `(U ⊗ V)(K) ≃ₜ U(K) × V(K)` (`schemeProductPointHomeomorph`).

## Étale morphisms

- `exists_isOpen_injOn_schemePointsMap`: if `X` is locally separated and `a : h_U → X` is
  étale, then `schemePointsMap a` is injective on an open neighbourhood of each point
  `u`. The diagonal section `δ : U → U ×_X U` is a section of the étale second
  projection, hence an open immersion, so its points form an open subset of
  `(U ×_X U)(K)`. By `isEmbedding_pairPullback_points` this open subset is the preimage
  of an open `G ⊆ U(K) × U(K)`, and `(u, u) ∈ G`. Choose `N₁ × N₂ ⊆ G` around `(u, u)` and
  put `N = N₁ ∩ N₂`. If `n, m ∈ N` have the same image in `X(K)`, they come from a point
  of `U ×_X U` mapping into `G`, hence from a point of the diagonal, so `n = m`.
- `isLocalHomeomorph_ringPointsMap`: for `f : X' ⟶ X` étale (`IsEtaleMorphism`) with
  `X'` quasi-separated and locally of finite type and `X` in the class of the corrected
  proposition, `RingPoints.map f` is a local homeomorphism. It is continuous
  (`continuous_ringPointsMap`) and open (`isOpenMap_ringPointsMap_of_isEtaleMorphism`).
  It is injective on the open set `c(N)` around each point `c(u)`. Here `c` is a chart of
  `X'` and `N` is a neighbourhood of `u` on which the étale map
  `hom c.hom ≫ hom f` is injective. So its restriction to `c(N)` is an open embedding.

## Fibre products

- `isEmbedding_pullbackPoints`: for a pullback square `P → X'`, `P → X''` over
  `X' → X ← X''` of presheaves of spaces, with `P`, `X'`, `X''` quasi-separated and
  locally of finite type and `X` in the class, the map
  `P(K) → X'(K) × X''(K)` is an embedding.
  - It is continuous by functoriality and injective because `P(K)` is the set-theoretic
    fibre product (`ext_app_of_isPullback`).
  - For the topology, let `O` be an open neighbourhood of `w ∈ P(K)`. Choose charts `c'`,
    `c''` through the images of `w`. Let `W = U' ×_X U''` be the pullback of the composite
    maps to `X`; it is locally of finite type and maps to `P` by the pullback property
    (`ρ`). The point `w` lifts to `w₀ ∈ W(K)`. The preimage of `O` under the continuous
    map `ρ` is open, hence of the form `W(K) ∩ G` by `isEmbedding_pairPullback_points`.
    Choose `N' × N'' ⊆ G` around the projections of `w₀`. Then `c'(N') × c''(N'')` is an
    open neighbourhood of the image of `w` (chart maps are open). Every point of `P(K)`
    over it comes from a point of `W(K)` in `N' × N''`, hence lies in `O`. So `O` is a
    neighbourhood of `w` for the induced topology (Mathlib's `isInducing_iff_nhds`).

Conrad's own argument for these two properties uses the identification
`(U ×_X U')(k) = U(k) ×_{X(k)} U'(k)` as topological spaces, which fails without local
separatedness. The proof here replaces it by `isEmbedding_pairPullback_points`.
