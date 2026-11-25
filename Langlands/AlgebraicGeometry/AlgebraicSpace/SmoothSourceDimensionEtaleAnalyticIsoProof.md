# Proof that étale maps are local analytic isomorphisms of the varying-dimension atlases

`smoothSourceDimensionEtaleAnalyticIso` proves the unchanged published
proposition
`Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionEtaleAnalyticIsoStatement.{u}`
in every universe `u`. The setting is a nontrivially normed henselian valued
field `K`, an admissible `σ : AnalyticPointStructure K`, and an étale morphism
`f : X ⟶ Y`. Here `X` and `Y` are smooth, quasi-separated, locally separated
algebraic spaces over `Spec K`. The theorem shows that `RingPoints.map f`
satisfies `DimensionPointAtlas.IsLocalAnalyticIso` between
`σ.dimensionAtlas` for `X` and for `Y`. The result supports Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.15, Proposition 5.4, and the final paragraph of its proof on
printed p.16 (`conrad-2011-weil-grothendieck-adelic-points`). There, étale
maps become local analytic isomorphisms, and smooth components may have
different dimensions. The proof follows the route the statement's Markdown
proposes. It uses only the admissibility premise and published Library
results. The axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Cancelling a monomorphism from an étale map

`IsEtale.of_comp_mono` is a small helper in category theory. It states that
if `g ≫ i` is relatively étale and `i` is a monomorphism of presheaves, then
`g` is relatively étale. For a representable `t` into the middle presheaf,
the square with sides `t`, `𝟙`, `i` and `t ≫ i` is a pullback, because `i` is
mono (`IsPullback.of_vert_isIso_mono`). Pasting pullback squares
(`IsPullback.paste_vert_iff`) then turns every represented pullback of
`g ≫ i` along `t ≫ i` into one of `g` along `t`, and the reverse. This lets
both parts of `IsEtale` (existence of a scheme pullback, and étaleness of
every represented pullback) pass from `g ≫ i` to `g`.

## Dimension preservation (namespace `SmoothDimensionPieces`)

- `pointDimension_map_of_isEtaleMorphism`: every point of `X` is the image
  of a point `u` of the chosen étale atlas of `X`, since the atlas is
  surjective on points. The composite of that atlas with `f` is an étale
  chart of `Y`, because `f` is an étale morphism. The published
  `pointDimension_chart` computes the intrinsic dimension of a point from
  any étale chart through it, as the local relative dimension of the chart
  scheme at `u`. Applied to `X` with its atlas and to `Y` with the
  composite chart, it gives the same number at `u`. So `f` preserves
  `pointDimension`.
- `fieldPointDimension_map_of_isEtaleMorphism` gives the same equality for
  field-valued sections. The Yoneda identity
  `uliftYonedaEquiv_symm_comp` (universe `u + 1`, as in `schemeYoneda`)
  identifies the chart of `RingPoints.map f x` with the chart of `x`
  followed by `f`. `Points.map_comp` then reduces this case to the previous
  one. This is the first conjunct of `IsLocalAnalyticIso`.

## Restricting `f` to the dimension pieces

- `preimage_subset_of_isEtaleMorphism`: by dimension preservation, the
  point preimage under `f` of the dimension-`n` locus of `Y` is the
  dimension-`n` locus of `X`.
- `range_le_of_isEtaleMorphism`: so the range of `inclusion ≫ f`, from the
  `n`-piece of `X`, lies in the open subfunctor of the `n`-piece of `Y`.
  This uses `Subfunctor.range_comp`, `image_le_iff` and
  `PointOpenSubspace.preimage`.
- `etaleRestriction hX hY hf n : space hX n ⟶ space hY n` is the factorization
  obtained by `Subfunctor.lift`. The lemmas `etaleRestriction_comp` and
  `etaleRestriction_ringPoints` record that it commutes with the two piece
  inclusions, on morphisms and on `L`-valued sections.
- `etaleRestriction_isEtaleMorphism`: take an étale chart `φ` of the
  `n`-piece of `X`. Then `φ ≫ inclusion` is étale, since open immersions
  are étale (`PointOpenSubspace.isEtale_of_isOpenImmersion`). Composing with
  `f` keeps it étale. That composite equals `(φ ≫ restriction) ≫ inclusion`
  on the `Y` side. The inclusion of a subfunctor is mono, so
  `IsEtale.of_comp_mono` shows `φ ≫ restriction` is étale. So the
  restriction is an étale morphism of pure `n`-dimensional spaces
  (`space_isSmoothPureDimensional`).

## Transport and chart lemmas (namespace `EtaleAnalyticIso`)

- `liftBoth e hi hj` transports an open partial homeomorphism `e : A → B`
  along open embeddings `i : A → A'` and `j : B → B'`. It applies Mathlib's
  `OpenPartialHomeomorph.lift_openEmbedding` twice, once on each side via
  `symm`; this needs `B` and `A'` to be nonempty. Its source and target are
  `i '' e.source` and `j '' e.target`, both by `rfl`. It satisfies
  `liftBoth (i a) = j (e a)` and `liftBoth.symm (j b) = i (e.symm b)`.
- `contDiffOn_chart_comp`: let `g` be `ContMDiffOn ω` between analytic
  manifolds modeled on normed spaces with the trivial model. Then, for
  atlas charts `d` and `d'`, the coordinate expression `d' ∘ g ∘ d.symm`
  is `ContDiffOn ω` on `d.target ∩ d.symm ⁻¹' (s ∩ g ⁻¹' d'.source)`. The
  proof is `contMDiffOn_iff_of_mem_maximalAtlas'` together with
  `IsManifold.subset_maximalAtlas`.
- `analyticOn_of_piece`: suppose `g` is `ContMDiffOn ω` on a set `s` of
  `K`-points of the `n`-piece of `X`, mapping into the `n`-piece of `Y`, for
  `σ`'s charted spaces. Suppose a map `G` of the original point spaces
  agrees with `inclusion ∘ g` on `s` and is continuous on `inclusion '' s`.
  Then `G` satisfies `DimensionPointAtlas.AnalyticOn` on `inclusion '' s`.
  Every chart of `σ.dimensionAtlas` is a `liftDimensionChart` of a chart of
  some piece `n₁` (source) or `m₁` (target). Consider a point of the test
  domain with `n₁ ≠ n`. It is the inclusion of a point of the `n`-piece and
  also of a point of the `n₁`-piece. `fieldPointDimension_map_inclusion`
  then gives two different values for its dimension, so the domain is
  empty. The same argument handles `m₁ ≠ n` on the target side, using the
  agreement `G = inclusion ∘ g`. When `n₁ = m₁ = n`, injectivity of the
  inclusion on points (`fieldPointInclusion_injective`) places each point
  of the domain inside the corresponding domain for the piece charts. There
  `G` read in the lifted charts equals `g` read in the piece charts,
  because `lift_openEmbedding_apply` evaluates the lifted target chart.
  `contDiffOn_chart_comp` then finishes, using the manifold instances
  supplied by `σ.IsAnalytic`.

## Branches and the final theorem

- `exists_branch`: let `y` be a `K`-point of the `n`-piece of `X`. Apply the
  étale-local-isomorphism part of `σ.IsAdmissible` (`hσ.2.2.1`) to the
  étale restriction of `f` to the `n`-pieces. It gives an analytic partial
  diffeomorphism `Φ`, with `y` in its source, that agrees with the
  restriction on its source. Its lift
  `e = liftBoth Φ (dimensionPiece_isOpenEmbedding ..) (dimensionPiece_isOpenEmbedding ..)`
  contains the inclusion of `y` in its source. It agrees with
  `RingPoints.map f` on its source by `liftBoth_apply` and
  `etaleRestriction_ringPoints`. `analyticOn_of_piece` makes it analytic on
  its source, applied to `Φ` with `Φ.contMDiffOn`. It also makes its
  inverse analytic on its target, applied to `Φ.symm` from `Y` to `X` with
  `Φ.symm.contMDiffOn`. The continuity inputs are `e.continuousOn` and
  `e.symm.continuousOn`. The nonemptiness instances needed by `liftBoth`
  come from the points at hand.
- `smoothSourceDimensionEtaleAnalyticIso`: the dimension conjunct is
  `fieldPointDimension_map_of_isEtaleMorphism`. Take a point `x`, let `n` be
  its intrinsic dimension, and apply `exists_branch` to `fieldPointFactor x`.
  The inclusion of that point is `x` itself (`fieldPointFactor_map`), which
  gives the branch at `x`.

No completeness, quasi-compactness, uniform or bounded dimension, or
nonemptiness hypothesis is used. Empty pieces and dimension zero need no
special treatment. The proof changes neither the target statement nor any
file it imports.
