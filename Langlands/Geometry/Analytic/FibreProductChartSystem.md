# The chart system of a fibre product of analytic spaces

Author: Worker 21.

Let `X`, `Y` and `S` be spaces with affinoid atlas presentations, and let
`f : X → S` and `g : Y → S` be compatible strong maps (`CompatibleStrongHom`,
whose bounded pullbacks are coherent). This module builds the gluing data of
the fibre product `X ×_S Y` and the glued space. It proves:

- the charts are the affinoid pushouts `O(V) ⊗_{O(W)} O(U)` for pairs of
  charts `V` of `X` and `U` of `Y` whose images lie in a common chart `W` of
  `S`, and they do not depend on the choice of `W`;
- these charts with componentwise inclusions form an `AffinoidChartSystem`;
- the two projections to `X` and `Y` are continuous and satisfy
  `f ∘ fst = g ∘ snd`;
- a point lies in the chart of a pair exactly when its projections lie in the
  two factor charts;
- if `X` and `Y` are Hausdorff, the chart system has finite overlaps and the
  charts are closed embeddings.

The atlas of the glued space and its universal property are not constructed
here (see Scope).

All declarations lie in `Langlands.Analytic.FibreProduct`, except the general
lemma `PresentedAffinoidAlgebra.represents_of_universal`. The field `K` is
complete, ultrametric and normed. The three presentations share the universes
`AffinoidAtlasPresentation.{u, v, w}`.

## Original source and derived provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`:

- Proposition 1.4.1, printed p.29 / PDF p.26: "The category Φ_k-𝒜n admits
  fibre products." The proof, for strong morphisms with nets `σ`, `τ`, `τ'`:
  "Let S denote the family of all triples (V, U, U'), where V ∈ σ, U ∈ τ,
  U' ∈ τ' and φ(V), f(U') ⊂ U. For α = (V, U, U') ∈ S we denote by W_α the
  k-affinoid space V ×_U U' …". The `W_α` are then glued by
  Proposition 1.3.3.
- Printed p.30 / PDF p.27: "the collection σ' of all affinoid domains of the
  form V ×_U U', where V ⊂ Y, U ⊂ X and U' ⊂ X' are Φ-affinoid domains with
  φ(V), f(U') ⊂ U, is a net on Y', and there is an evident Φ_k-affinoid atlas
  with the net σ'."

The construction follows these triples, with derived choices:

- Charts are indexed by pairs `(V, U)` of charts of `X` and `Y` that admit a
  common base chart `W`, not by triples. A base chart is chosen for each pair,
  and `condition_of_isCommonBase` shows that nothing depends on the choice.
  Triples `(V, W, U)` and `(V, W', U)` would give the same chart of the glued
  space twice.
- The algebra of `V ×_W U` is the Library's affinoid pushout
  `AffinoidPushout.algebra` of the two pullbacks `O(W) → O(V)` and
  `O(W) → O(U)`. It has the pushout property for maps into presented affinoid
  algebras.
- The gluing uses the Library's `AffinoidChartGluing`. Its data are a preorder
  of affinoid domain inclusions between charts, not Berkovich's pairwise
  isomorphisms `ν_{αβ}`.
- The finite-overlap theorem follows the Library's `AffinoidProductChartSystem`
  for absolute products: finite overlaps come from the Hausdorff property of
  `X` and `Y`.

## Representing a domain through its universal property

`PresentedAffinoidAlgebra.represents_of_universal`: let `i : B → A` be a
bounded map whose spectrum image lies in the locus of a domain `D` of `B`,
and which has the universal factorization property for that locus. Then `i`
represents the locus. The domain `D` factors through `i`, which gives the
reverse inclusion of spectrum images.

## Independence of the base chart

`IsCommonBase f g i j k`: the images of the chart `i` of `X` and the chart `j`
of `Y` lie in the chart `k` of `S`.

`condition_of_isCommonBase`: if `α ∘ f_k^* = β ∘ g_k^*` for maps
`α : O(V_i) → T`, `β : O(U_j) → T` and one common base chart `k`, then the
same holds for every other common base chart `k'`. By coherence of `f` and `g`
(`IsMapChartChange`, stable under postcomposition) both sides over `k'` are
target chart changes, from `k` to `k'`, of the same map `O(W_k) → T`. The
Library's uniqueness of chart change (`eq_changeMapChart`) identifies them.

## The chart system

- `PairIndex f g`: pairs of charts that have a common base chart. `base` is a
  chosen one, `leftBase` and `rightBase` are the two pullbacks from it.
- `algebra f g p`: the affinoid pushout over the chosen base. `leftMap` and
  `rightMap` are its two legs. `condition`: the pushout square holds over
  every common base chart.
- `Sub f g p q`: componentwise inclusion of chart ranges. A common base chart
  of `q` is one of `p` (`IsCommonBase.mono`).
- `restriction f g p q h : O(q) → O(p)` is the pushout lift of the two legs of
  `p` composed with the atlas restrictions. Compatibility
  (`restriction_compat`) uses the restriction equations of the strong maps and
  `condition` over the base chart of `q`. `restriction_comp_leftMap` and
  `restriction_comp_rightMap` are the two lift identities.
  `restriction_refl` and `restriction_trans` follow from the pushout
  uniqueness `AffinoidPushout.hom_ext`.
- `leftPoint` and `rightPoint` are the two projections of a point of a pair
  chart; `leftPoint_pull`, `rightPoint_pull`, `chart_leftPoint_pull` and
  `chart_rightPoint_pull` compute them on pulled-back points.
- `subDomain f g p q h` is the domain of `O(q)` whose locus consists of the
  points with projections in the charts of `p`
  (`mem_subDomain_locus`). It is the intersection of the Library's inverse
  image domains (`Domain.pullback`) of the two atlas restriction domains.
- `restriction_universal`: the restriction has the universal factorization
  property for this locus. The two legs of a test map factor through the
  atlas restrictions by the atlas universal property. The factorizations are
  compatible over the base chart of `q`, hence over the base chart of `p` by
  `condition_of_isCommonBase`, and the pushout lift is the factorization.
- `represents_restriction`, `range_restriction`, `mem_range_restriction_iff`:
  the restriction represents this locus, which is its spectrum image.
- `chartSystem f g : AffinoidChartSystem K` assembles these data. Its meet
  property uses the Library's `exists_chart_inter` in `X` and in `Y`; a pair of
  subcharts of a pair with a common base chart has the same common base chart.

## Projections

- `fst f g`, `snd f g`: the maps from the glued space to `X` and `Y` given on
  the chart of `p` by the projection points composed with the charts
  (`fst_chart`, `snd_chart`). They are well defined because glued points are
  pullbacks of one point of a common subchart, and continuous
  (`continuous_fst`, `continuous_snd`).
- `baseMap_fst`: `f (fst z) = g (snd z)`, from the chart equations of the strong
  maps and the pushout condition.
- `mem_range_chart_iff`, `range_chart`: the chart of `p` is
  `fst⁻¹(V_p) ∩ snd⁻¹(U_p)`. For the reverse inclusion, write the point in
  some chart `q`, choose charts through the projections inside both chart
  ranges (`exists_chart_inter`), and pull back from the resulting common
  subchart of `p` and `q`.

## Finite overlaps

- `hasFiniteOverlaps`: if `X` and `Y` are Hausdorff, glued points of two pair
  charts come from finitely many common subcharts. The intersections of the
  factor chart ranges are compact and covered by finitely many charts
  contained in them (Library `exists_finite_charts_inter`). The pairs of such
  charts share the base chart of the first pair.
- `isClosedEmbedding_chart`: under the same hypothesis the charts are closed
  embeddings (Library `isClosedEmbedding_chart` of `AffinoidChartGluing`).

## Scope

Not constructed here: the indexed affinoid atlas of the glued space (nets,
restrictions between charts with included ranges, Hausdorffness), the
projections as strong maps, and the universal property of the fibre product.
The base chart system is defined for arbitrary atlas presentations. That the
pairs cover the whole fibre product, as in Berkovich's construction, needs
atlases containing all local affinoid domains and is not used here.
