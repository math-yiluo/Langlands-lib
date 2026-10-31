# Strong inverses for quasi-isomorphisms with upper-cofinal chart images

This module constructs a full reverse strong morphism from the actual bounded
pullbacks of a strong quasi-isomorphism. The target atlas must have directed
original charts, and every original target chart must be contained in the image
of some original source chart. The reverse map is itself a full
quasi-isomorphism. When the source atlas also has directed charts, both
composites are the full strong identities, giving an actual isomorphism in
`DirectedAtlasPresentation`.

## Sources and provenance

The original source is Vladimir G. Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Definition 1.2.3 and Remark 1.2.4(i), printed page 16 / PDF page 13,
specify affinoid atlases and compatible bounded restrictions.
Definition 1.2.7, printed page 18 / PDF page 15, requires a strong morphism to
have compatible affinoid morphisms at every admissible original chart pair.
Definition 1.2.9, printed page 19 / PDF page 16, specifies quasi-isomorphisms by
an ambient homeomorphism and affinoid-domain identifications. Proposition
1.2.10(d) and its proof, printed pages 19–20 / PDF pages 16–17, provide the
algebraic cancellation principle used through the published
`StrongQuasiIsoCancellation` module.

The present construction is a derived consequence for the existing atlas
implementation. Its upper-cofinal chart-image condition and directedness
hypotheses are additional assumptions on the supplied original atlases. The
source does not state that every strong quasi-isomorphism has a strong inverse;
its general analytic category is obtained by localization. This module proves
actual invertibility under the explicit additional hypotheses.

## Data and hypotheses

The scalar field `K : Type u` is a complete normed ultrametric field. The
ambient-space universe `v` and chart-index universe `w` remain independent of
`u`. Let `A` and `B` be `AffinoidAtlasPresentation.{u,v,w} K`, let
`f : StrongHom A B`, and let `hf : f.IsQuasiIso`. Write `A_i` and `B_j` for
the actual presented chart algebras, `V_i` and `W_j` for their embedded
spectrum ranges, and `f_iq : B_q → A_i` for the bounded pullback whenever
`f(V_i) ⊆ W_q`.

`HasUpperCofinalImage f` is the proposition

```text
∀ j, ∃ i, W_j ⊆ f(V_i).
```

The witnesses range over the original chart indices. Directedness of `B` means
that any two original chart ranges are contained in a third original chart
range. These are the existing `HasDirectedCharts` conditions. The construction
requires no ordering or monotonicity of the choices of upper charts or of the
witnesses to upper cofinality.

Every occurrence of domain representation uses the published
`PresentedAffinoidAlgebra.Represents`. This includes closedness, the exact
spectrum image and unique bounded algebra factorization against every
`R : PresentedAffinoidAlgebra K`, retaining the full finite positive-polyradius
test class. The bounded maps are maps between the supplied original chart
algebras.

## Construction and implemented proof

For `W_j ⊆ f(V_i)`, choose an original target chart `W_q` containing both
`f(V_i)` and `W_j`. The restriction `B_q → B_j` has spectrum image in the
domain represented by `f_iq`. Its full factorization property therefore
constructs a bounded map `ψ_ji : A_i → B_j` with

```text
ψ_ji.comp f_iq = B.restriction j q.
```

`inversePullback_existsUnique` strengthens this equation to every common
containing target chart `q`, and proves uniqueness with this characterization.
To pass between two containing charts, the proof uses a common upper chart,
the compatibility equations of `f`, the original restriction composition law,
and `restriction_hom_ext`. Uniqueness of `ψ_ji` itself follows from full domain
factorization uniqueness. `inversePullback` chooses this unique bounded map,
and `inversePullback_comp_pullback` exposes its characterization.

Applying the spectrum functor to the factorization equation and using the two
chart squares proves `inversePullback_chart`:

```text
f (A.chart i (comap ψ_ji x)) = B.chart j x.
```

For inclusions `W_j ⊆ W_j'` and `V_i ⊆ V_i'`, with both reverse pairs
admissible, `inversePullback_naturality` proves the bounded-map equation

```text
(B.restriction j j').comp ψ_j'i' =
  ψ_ji.comp (A.restriction i i').
```

The proof chooses a common target chart containing `f(V_i')` and `W_j'`,
then compares these two maps using full domain uniqueness and the
factorization equations. Thus it proves compatibility of bounded algebra
maps, including their algebraic information.

`inverseBaseMap` is the continuous inverse of the actual ambient
homeomorphism supplied by `hf`. Its two pointwise inverse equations are
`baseMap_inverseBaseMap` and `inverseBaseMap_baseMap`.
`inverse_admissible_iff` identifies an admissible reverse chart pair with the
containment `W_j ⊆ f(V_i)`. The definition `inverse hb hc` uses upper cofinality
`hc` for the strong-map target-existence field, the constructed bounded
`inversePullback` at every admissible reverse pair, its spectrum square for
`chart_comm`, and its naturality for `restriction_comm`.
`inverse_baseMap` and `inverse_pullback` expose these actual components.

`inverse_isQuasiIso` proves full domain representation for each reverse
pullback. With `q` as above, the composite `ψ_ji.comp f_iq` is the original
restriction `B_q → B_j`, which already represents its full relative domain.
The published `Represents.of_comp_of_injective` then gives representation for
`ψ_ji` on the inverse-image locus. Its injectivity premise is supplied by
`hf.isEmbedding_pullback`, whose embedding proof comes from the ambient
homeomorphism and the two embedded charts. The chart square and the inverse
homeomorphism equations identify this locus with the reverse map's
`chartImageLocus`. The reverse homeomorphism supplies the remaining
quasi-isomorphism field. This part requires directedness of `B` only.

With directedness of `A` as well, `inverse_comp` proves

```text
(hf.inverse hb hc).compOfDirected f ha hb = StrongHom.id B.
```

It first proves the equality of ambient maps and then applies
`ext_of_directed`. At a cofinal reverse chart pair, the factorization equation
identifies the actual composite pullback with the original restriction
defining the identity. `comp_inverse` proves

```text
f.compOfDirected (hf.inverse hb hc) hb ha = StrongHom.id A
```

by cancellation after composition with `f`, using the published algebraic
`cancel_compOfDirected`, associativity, and the already proved inverse
equation. These are equalities of full strong maps.

Finally, `DirectedAtlasPresentation.cofinalImageIso f hf hc : A ≅ B` packages
`f` and the constructed inverse in the existing full directed strong-map
category. Its category inverse laws are precisely `comp_inverse` and
`inverse_comp`. `cofinalImageIso_hom` and `cofinalImageIso_inv_baseMap`
record the forward arrow and the reverse underlying continuous map.

## Scope

This is a construction for the explicit original-chart directed category.
General atlas extension and gluing, the unrestricted fraction category, and
étale or equivariant site constructions remain separate obligations. The
present module imports the published composition and cancellation results by
Lean module name and supplies every reverse bounded map and both inverse laws.
