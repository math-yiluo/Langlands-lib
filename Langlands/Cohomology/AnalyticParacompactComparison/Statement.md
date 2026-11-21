# Ordinary cohomology of the restriction on paracompact analytic spaces

Author: Worker 16.

## Source

Vladimir Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996 unfinished manuscript), [Theorem 1.6.1(i), pp. 13–14](https://www.wisdom.weizmann.ac.il/~vova/Equish_1996.pdf#page=13)
(printed and PDF pagination). Registered literature ID
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
folder SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
PDF SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

For a paracompact analytic `G`-space `X`, part (i) says that the right
derived functors of `F ↦ (b^*F)(X)` on abelian sheaves on `X(G)` have
values `H^q(X, b^*F)`, for the étale and quasi-étale sites separately.
Here `b : X → X(G)` is the morphism of sites in §1.2 and `b^*` is its
inverse image. In particular, the functor being derived is **ordinary
sections after restriction**. Neither the derived smooth sections of
part (ii), the invariant sections of §1.2, nor the compactly supported
sections of §1.5 occur in part (i).

## Model and scope

The two propositions work in the Library's `EtaleGSheaf` and
`QuasiEtaleGSheaf` models, with `etaleGSheafRestriction` and
`quasiEtaleGSheafRestriction` in place of `b^*`. Theorem 1.4.2, pp. 8–9,
identifies sheaves on the manuscript's equivariant sites with smooth
`G`-sheaves there. A formal comparison transporting the Library models
and their functors to those sites is still open; see the
[modelling choices](../AnalyticGlobalComposite/Statement.md#correspondence-and-modelling-choices).
In the quasi-étale case the ordinary target uses the existing
`quasiEtaleTopology` and the source uses `twistedQuasiEtaleTopology`.
The comparison does not identify them with the manuscript topologies
or use the compact-probe replacement for the ordinary topology.

The inputs are a complete ultrametric normed field `K : Type u`, an
analytic space `X : LocalizedCategory.{u,v,v} (K := K)`, a topological
group `G : Type z`, and `ρ : G →* Aut X`. The two propositions assume
`T2Space` and `ParacompactSpace` on `localizedSpaceFunctor.obj X`, and
`IsContinuousAction ρ`. Hausdorffness and continuity are standing source
conditions (§1.1, pp. 1–2); paracompactness is the hypothesis of (i).
The action is over the fixed field `K`, unlike the source's allowance for
isometric automorphisms of the base field (§1.1, p. 1). There is no
compactness premise on `X` or `G`.

Write `s = max u (v + 1) uL`. The retained size hypothesis is
`Small.{s} G`, with `HasAdmissibleRefinements` for the distinguished
lifts on the twisted étale site or `HasFiniteEquivariantRefinements`
for the compact lifts on the twisted quasi-étale site. These are inputs
of the Library model, not consequences of paracompactness asserted here.
Coefficients are modules over one commutative ring `R : Type s`, in
particular integer modules (with a universe lift if needed) for abelian
sheaves. Both sides take values in `ModuleCat.{s} R`; no change of
coefficients or action on the output is part of this comparison.

## Lean declarations

The declarations are in `Langlands.Cohomology.AnalyticParacompactComparison`.
The comparison functors in degree `q : ℕ` are

\[
R^q(\Gamma_X \circ b^*) \;\longrightarrow\; (R^q\Gamma_X) \circ b^* .
\]

* `etaleRestrictedSectionsComparison` and
  `quasiEtaleRestrictedSectionsComparison` define this comparison as
  the natural transformation `ExactBaseChange.compComparisonNatTrans`
  along the exact restriction functor. Its source derives the composite
  on the category of equivariant sheaves; its target derives ordinary
  sections on the category of ordinary sheaves *before* composing with
  restriction. No choice of an arbitrary isomorphism is used.
* `AnalyticEtaleParacompactComparisonStatement` and
  `AnalyticQuasiEtaleParacompactComparisonStatement` assert that this
  specified natural transformation is an isomorphism in every degree,
  with the hypotheses above. In particular this is a natural
  `R`-linear comparison in the sheaf argument, not just a group
  isomorphism at each object.

## Proof boundary

These are statements. Exactness of restriction defines the map; it
does not alone make the map invertible. By
`ExactBaseChange.compComparisonNatTrans_app` and
`AcyclicResolution.isIso_compComparison`, the needed acyclicity is
vanishing of higher ordinary global cohomology for restrictions of
injective equivariant sheaves. For the étale case the manuscript invokes
Proposition 1.5.1 (pp. 10–11, softness of restricted Godement terms) and
Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. **115**
(1994), Lemma 3.2(i), printed p. 544 / PDF p. 6 (ordinary acyclicity of
soft étale sheaves on paracompact spaces). The latter source is registered
as `berkovich-1994-vanishing-cycles-formal-schemes`, SHA-256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.
For the quasi-étale case the manuscript first treats compact bases with
finite covers, then uses a comparison of `R^q μ_*` along restriction and
the étale result (pp. 13–14). Neither proof of paracompact comparison is
supplied here.
