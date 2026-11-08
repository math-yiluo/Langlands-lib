# Gluing affinoid spectra along affinoid domain inclusions

Author: Worker 36.

This module constructs a topological space by gluing the spectra of a family
of presented affinoid algebras along affinoid domain inclusions. It proves
that the charts are continuous and injective. Under a finite-overlap condition
they are closed embeddings. It also proves a general topological lemma: a
space covered by finitely many closed Hausdorff subspaces is Hausdorff. This
is the gluing step needed to build new analytic spaces, in particular products
and fibre products, from affinoid charts.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Before Proposition 1.3.3, printed p.24 / PDF p.21, Berkovich considers spaces
`Xᵢ` with analytic domains `Xᵢⱼ ⊂ Xᵢ` and isomorphisms `νᵢⱼ : Xᵢⱼ ⥲ Xⱼᵢ`, and
looks for a space `X` obtained by gluing. Proposition 1.3.3 states that the
glued space exists and is unique in each of two cases: (a) all `Xᵢⱼ` are open
in `Xᵢ`; (b) for any `i`, all `Xᵢⱼ` are closed in `Xᵢ` and the number of `j`
with `Xᵢⱼ ≠ ∅` is finite. Its proof takes the quotient `X̃/R` of the disjoint
union `X̃ = ∐ᵢ Xᵢ` by the equivalence relation defined by the `νᵢⱼ`.

The construction here follows that proof: the glued space is the quotient of
the disjoint union of the chart spectra by an equivalence relation, with the
quotient topology. The gluing data are derived. They are given by a preorder of
affinoid domain inclusions between the charts, not by the pairwise
isomorphisms `νᵢⱼ`. The finite-overlap condition used for closed embeddings
is also derived. It replaces the local finiteness of case (b): a chart may meet
infinitely many others, provided each overlap is covered by finitely many
common subdomains. The analytic structure of the glued space (its atlas, nets
and restriction maps) is not constructed here.

## Chart systems

`AffinoidChartSystem K` consists of:

- an index type `Index` and presented affinoid algebras `algebra i`;
- a relation `Sub i j` ("`i` is a subdomain of `j`") with bounded restriction
  maps `restriction i j h : algebra j → algebra i`;
- reflexivity and transitivity of `Sub`, with `restriction i i = id` and
  `restriction i k = restriction i j ∘ restriction j k`;
- `represents`: each restriction represents its spectrum image, so it is an
  affinoid domain in the sense of the Library's `Represents`;
- `meet`: if a point `t` of chart `k` lies in the images of two subdomains `i`
  and `j` of `k`, then some `l` with `Sub l i` and `Sub l j` also contains `t`
  in its image.

`pull h` is the spectrum map of the restriction of `h`. `toDomain h` is the
corresponding Library `Domain`, so `pull_injective` follows from the Library's
`Domain.spectrumMap_injective`. `pull_refl` and `pull_trans` record
functoriality. `continuous_pull` records continuity.

## The glued space

`Glued i s j t` says that the points `s` of chart `i` and `t` of chart `j` are
the pullbacks of one point of a common subdomain.

- `glued_refl` and `glued_symm` are immediate.
- `exists_common`: if two subdomain points have the same image in a common
  chart, the meet property gives a smaller common subdomain through the image.
  Injectivity of pullbacks identifies the corresponding point with both
  given points.
- `glued_trans` composes two gluings through such a common subdomain.

`setoid` is the resulting equivalence relation on the disjoint union
`Σ i, BanachSpectrum (algebra i)`. `Space` is its quotient with the quotient
topology. `chart i` is the composite of the inclusion of the `i`-th spectrum
and the quotient map.

- `chart_eq_iff`: two chart points have the same image exactly when they are
  glued.
- `continuous_chart`: charts are continuous.
- `chart_injective`: a point glued to itself through a subdomain is a single
  pullback, so charts are injective.
- `chart_pull`: a chart point pulled back from a subdomain has the same image
  as the subdomain point.
- `exists_chart`: every point of the glued space lies in some chart.

## Closed charts under finite overlaps

`HasFiniteOverlaps` asks that for any two charts `i`, `j` there is a finite
set of common subdomains (indices `k` with `Sub k i` and `Sub k j`) through
which every gluing of a point of `i` with a point of `j` takes place.

`isClosed_chart_preimage_image`: under finite overlaps, for a closed set `F` in
chart `i`, the preimage in chart `j` of its image is closed. It equals the
finite union, over the given common subdomains `k`, of the images in chart `j`
of the preimages of `F` in chart `k`. Each preimage is closed in a compact
spectrum, hence compact; its image is compact in the Hausdorff spectrum of
chart `j`, hence closed.

`isClosedEmbedding_chart`: under finite overlaps every chart is a closed
embedding. A subset of the quotient is closed when its preimage in every
summand of the disjoint union is closed. The preceding lemma therefore shows
that charts are closed maps. They are continuous and injective.
`isClosed_range_chart` follows.

## Finite closed Hausdorff covers

`t2Space_of_finite_isClosed_cover`: if a space is covered by finitely many
closed subsets, each Hausdorff in its subspace topology, then it is Hausdorff.
For distinct points `a`, `b`, take in each member containing both an ambient
pair of open sets separating them within the member. Then
`U = ⋂ᵢ (Oᵢ ∪ Cᵢᶜ, univ or Cᵢᶜ)` and the analogous `V` are open, contain `a` and
`b`, and are disjoint. A common point would lie in a member `Cᵢ`, which then
contains both `a` and `b`, and in both separating sets of that member.

## Scope

The atlas of the glued space, its nets, the restriction maps between nested
chart ranges, and its local Hausdorffness are not constructed here. The same
holds for products and fibre products of analytic spaces.
