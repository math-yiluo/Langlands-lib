# The affinoid atlas of the product of two Hausdorff analytic spaces

Author: Worker 21.

The Library module `AffinoidProductChartSystem` glues the affinoid
coproducts of pairs of charts of two indexed affinoid atlases into a
topological space. It defines the two projections and proves that the
product charts are closed embeddings when both spaces are Hausdorff. Its
scope note leaves the atlas of the glued product as further work, along with
its Hausdorffness, the projections as morphisms and the universal property.

This module constructs that atlas. For Hausdorff `X` and `Y` with indexed
affinoid atlases `a` and `b`, it proves:

- the glued product is Hausdorff;
- the product charts with nonempty factors form an `IndexedAffinoidAtlas` on
  it, with the coproduct restrictions as restriction maps;
- the two projections are compatible systems of bounded maps on all
  admissible chart pairs (`AdmissiblePairSystem`), and every product chart
  maps into a chart of each factor.

It does not prove the universal property of the product, and it does not
construct fibre products over a base.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

- Proposition 1.4.1, printed p.29 / PDF p.26: "The category Φ_k-𝒜n admits
  fibre products." For strong morphisms to `X` from `Y` and from `X'`, the
  proof takes the triples `(V, U, U')` of net members with
  `φ(V), f(U') ⊂ U` and the k-affinoid spaces `W_α = V ×_U U'`, and glues them
  by Proposition 1.3.3. In the case where only `X` is paracompact it states:
  "The collection σ' of sets of the forms V ×_U U', where V ⊂ Y_i, U ⊂ X and
  U' ⊂ X'_j are affinoid domains, is a net of compact subsets on Y', and
  there is an evident k-affinoid atlas ℬ' with the net σ'."
- Continuation of the proof, printed p.30 / PDF p.27: for affinoid domains
  `V ⊂ Y`, `U ⊂ X` and `U' ⊂ X'` with `φ(V), f(U') ⊂ U`, "the canonical
  morphism V' := V ×_U U' → Y' identifies V' with an affinoid domain in Y'".
  It also states: "It is easy to see that the canonical projections Y' → Y
  and Y' → X' are morphisms of Φ_k-analytic spaces and that Y' is a fibre
  product of Y and X' over X in the category Φ_k-𝒜n."

The absolute product is the case in which the base is the one-point space
`𝓜(k)` with its single chart. The triples are then pairs of charts, and
`V ×_U U'` is the coproduct of the two chart algebras. This module transcribes
the "evident" atlas of this case and the projections. Berkovich gives no
details here, so the following choices and proofs are derived:

- The indices are the pairs of charts whose two chart domains are nonempty.
  Pairs with an empty factor have empty product charts. The Library's atlas
  structure requires distinct indices to have distinct chart ranges, so at
  most one chart may be empty; the empty pairs are therefore left out.
- Hausdorffness of both factors is assumed. The same hypothesis is used by
  `isClosedEmbedding_productChart`. Berkovich's equivariant manuscript,
  registered as
  `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
  (folder SHA256
  `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`; file
  `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`),
  §1.1, printed p.1, states: "In what follows all analytic spaces considered
  are assumed to be Hausdorff."
- The proofs of the net property, of Hausdorffness and of the chart
  identities are derived.

## Nets of preimage intersections

In `Langlands.Analytic.AtlasTopology`, for maps `f : Z → X`, `g : Z → Y`
and families `τ` on `X`, `υ` on `Y`:

- `preimageProductFamily f g τ υ` is the family of nonempty sets
  `f ⁻¹' U ∩ g ⁻¹' V` with `U ∈ τ` and `V ∈ υ`.
- `IsQuasinet.preimageProductFamily`: for continuous `f` and `g`, if `τ` and
  `υ` are quasinets then so is this family. At `z`, take the finite families
  of `τ` at `f z` and of `υ` at `g z`. The preimage intersections of their
  members contain `z`, and their union contains the intersection of the
  preimages of the two unions, which is a neighborhood of `z`.
- `locallyRefines_preimageProductFamily`: the same construction with
  neighborhoods within subspaces. If `τ` refines `S` and `υ` refines `T` in
  the sense of the Library's `LocallyRefines`, then the family refines
  `f ⁻¹' S ∩ g ⁻¹' T`. The proof uses continuity within the subspace.
- `IsNet.preimageProductFamily`: for continuous `f`, `g`, if `τ` and `υ` are
  nets then so is the family. The intersection of two members
  `f ⁻¹' U₁ ∩ g ⁻¹' V₁` and `f ⁻¹' U₂ ∩ g ⁻¹' V₂` is
  `f ⁻¹' (U₁ ∩ U₂) ∩ g ⁻¹' (V₁ ∩ V₂)`. The Library equivalence
  `isQuasinet_restrictedFamily_iff` turns the net conditions of `τ` and `υ`
  into refinements of `U₁ ∩ U₂` and `V₁ ∩ V₂`, and the previous lemma applies.

`t2Space_of_separated_or_open_t2` is a topological criterion. A space is
Hausdorff if any two distinct points are either separated by disjoint open
sets or lie in a common open subset that is Hausdorff in the subspace
topology. Open sets of an open subspace are open in the space.

## Points of the affinoid coproduct

- The `Subsingleton` instance on `BanachSpectrum (initialAlgebra K)`: the
  constructed scalar presentation has at most one spectrum point. Every
  element is the image of a scalar, because `scalarInclusion` composed with
  `initialMap` is the identity by `initial_hom_ext`. Every point takes the
  value `‖c‖` on the scalar `c` (Library `BanachSpectrum.algebraMap_apply`).
- `AffinoidCoproduct.exists_point`: any points `x` of `A` and `y` of `B` are
  the projections of a point of `AffinoidCoproduct.algebra K A B`. The
  coproduct is the Library's pushout over the scalar presentation, so this
  is the Library's `AffinoidPushout.exists_point` (based on the proved point
  amalgamation). Its compatibility hypothesis holds because the scalar
  presentation has a single point.

## The product atlas

Let `a : IndexedAffinoidAtlas K X` and `b : IndexedAffinoidAtlas K Y`, and
let `C = productChartSystem a b`, with glued space `C.Space` and projections
`productFst`, `productSnd`.

- `exists_productPoint`: for a pair `p` of charts, points of the two factor
  charts are the projections (`leftPoint`, `rightPoint`) of a point of the
  product chart.
- `mem_range_productChart_iff` and `range_productChart`: a point of the glued
  space lies in the product chart `p` exactly when its two projections lie in
  the chart ranges of `p.1` and `p.2`:

  ```text
  range (C.chart p) = productFst ⁻¹' range (a.chart p.1) ∩ productSnd ⁻¹' range (b.chart p.2)
  ```

  For the reverse inclusion, write the point as `C.chart q t`. The net axioms
  of the factor atlases give charts `m₁`, `m₂` through the two projections
  inside the intersections of the chart ranges of `p` and `q`. The Library
  criterion `mem_range_productRestriction_iff` writes `t` as a pullback from
  `(m₁, m₂)`, which is a subchart of `p`.
- `range_productChart_subset`: componentwise inclusion (`ProductSub`) gives
  inclusion of product chart ranges.
- `ProductIndex a b` is the subtype of pairs `p` whose factor chart ranges are
  both nonempty. `range_productChart_nonempty` shows that the product chart of
  such a pair is nonempty, by `exists_productPoint`.
- `productSub_of_range_subset`: if `p` is in `ProductIndex a b` and the
  product chart of `p` is contained in that of `q`, then `p` and `q` satisfy
  `ProductSub`. A point `x` of the first factor chart of `p` is the first
  projection of a point of the product chart of `p`, since the second factor
  is nonempty. Its image lies in the product chart of `q`, so `x` lies in the
  first factor chart of `q`. The second factor is symmetric.
- `productChartFamily_eq`: the family of product chart ranges indexed by
  `ProductIndex a b` equals `preimageProductFamily productFst productSnd` of
  the two factor chart families. `isNet_productChartFamily`: it is a net, by
  `IsNet.preimageProductFamily` and continuity of the projections.
- `t2Space_productSpace`: for Hausdorff `X` and `Y`, the glued product is
  Hausdorff. Points with different first or second projections are separated
  by preimages of disjoint open sets. For points `z ≠ z'` with equal
  projections, take finite families `σ` in `X` and `σ'` in `Y` of chart ranges
  whose unions are neighborhoods of the projections (quasinet axiom). The set
  `N`, the intersection of the preimages of the interiors of the two unions,
  is open and contains `z` and `z'`. It lies in the set `F`, the intersection
  of the preimages of the two unions. `F` is covered by the finitely many
  sets `productFst ⁻¹' U ∩ productSnd ⁻¹' V` with `U ∈ σ`, `V ∈ σ'`. Each is
  closed: factor chart ranges are compact in Hausdorff spaces, hence closed.
  Each is Hausdorff, since by `range_productChart` it lies in a product chart
  range, which is homeomorphic to a spectrum. The Library's
  `t2Space_of_finite_isClosed_cover` makes `F` Hausdorff, so `N` is
  Hausdorff, and the criterion above applies.
- `productAtlas a b : IndexedAffinoidAtlas K C.Space`, for Hausdorff `X` and
  `Y`, has:
  - indices `ProductIndex a b`;
  - algebras `productAlgebra a b p`, the affinoid coproducts
    `AffinoidCoproduct.algebra K (a.algebra p.1) (b.algebra p.2)`;
  - charts `C.chart p`, which are embeddings by
    `isClosedEmbedding_productChart`;
  - injective chart ranges: equal ranges give `ProductSub` in both
    directions, hence equal factor chart ranges, hence equal indices by
    injectivity in `a` and `b`;
  - local Hausdorffness from `t2Space_productSpace`, with the whole space as
    neighborhood;
  - the net `isNet_productChartFamily`;
  - restrictions `productRestriction a b p q` along the inclusion given by
    `productSub_of_range_subset`, with the chart equation `C.chart_pull`;
  - the universal property from `represents_productRestriction`. If a
    bounded map `φ` from the algebra of `q` to a presented affinoid algebra
    has all spectrum images in the chart range of `p`, then by
    `mem_range_productChart_iff` and `mem_range_productRestriction_iff` these
    images lie in the represented locus of the restriction, so `φ` factors
    uniquely;
  - identity and composition laws from `productRestriction_refl` and
    `productRestriction_trans`.

  Its universe parameters are `u` for the field, `max u w w'` for the glued
  space and `max w w'` for the indices.
- `productPresentation a b` bundles the glued space as a `TopCat` with this
  atlas.

## The projections

- `productFst_image_range`, `productSnd_image_range`: for `p` in
  `ProductIndex a b`, the first (second) projection maps the product chart of
  `p` onto the chart range of `p.1` (`p.2`). The proof uses
  `exists_productPoint` with a point of the other, nonempty factor.

For Hausdorff atlas presentations `P` and `Q`,
`AffinoidAtlasPresentation.product P Q` is
`productPresentation P.atlas Q.atlas`.

- `AffinoidAtlasPresentation.productFst P Q : AdmissiblePairSystem (product P Q) P`
  has ambient map `productFst`. For a product chart `p` and a chart `i` of
  `P` containing the image of the product chart, its bounded map from the
  algebra of `i` is the first coproduct leg composed with the atlas
  restriction from `i` to `p.1`. That restriction exists because the image of
  the product chart is the chart range of `p.1`. The chart equation follows
  from `restriction_chart`. The restriction law follows from
  `productRestriction_comp_leftMap` and two instances of `restriction_comp`.
- `productFst_target_exists`: every product chart maps into the chart `p.1`
  of `P`.
- `productSnd` and `productSnd_target_exists` are the same constructions for
  the second factor, with the second coproduct leg.

`AdmissiblePairSystem` allows source and target presentations in different
universes, as is the case here. When the universes agree, the Library's
`AdmissiblePairSystem.toStrongHom` turns these systems with the target
existence lemmas into strong maps.

## Scope

The coefficient field is a complete ultrametric normed field; trivial
valuations are allowed. The following are not proved here: the universal
property of the product among analytic spaces or strong maps; fibre products
over a nontrivial base, where Berkovich's triples `(V, U, U')` depend on a
base chart; base change of étale morphisms; and the étale, quasi-étale and
equivariant sites.
