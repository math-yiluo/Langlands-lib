# Étale compact-support spectral sequence on a compact analytic base

Author: Worker 16.

## Source and specialization

Vladimir Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996 unfinished manuscript), [Corollary 1.5.2(i), pp. 11–12](https://www.wisdom.weizmann.ac.il/~vova/Equish_1996.pdf#page=11)
(printed and PDF pagination). Registered literature ID
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
folder SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
PDF SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The **étale** spectral sequence displayed at the top of p. 12 has

\[
E_2^{p,q}=H^p(G,H^q_c(X,b^*F)) \quad\Longrightarrow\quad H^{p+q}_c(X(G),F).
\]

This module states the compact-base specialization in the Library's
model. In addition to the usual model hypotheses, `X` is assumed to
be compact Hausdorff and covered by the given `L`-valued points. The
compactness assumption is essential to this formulation's route from
ordinary cohomology. Without a restriction on the scope, the source
spectral sequence fails: see the analytic disjoint-point translation
example in [EquivariantComposite/Statement.md](../EquivariantComposite/Statement.md#truth-argument).
The example concerns the abutment of the spectral sequence, not the
separate comparison `H^q_c(X{G},F) → H^q_c(X,b^*F)`.

The derived equivariant functors here are in `EtaleGSheaf`, not in the
manuscript's equivariant site. A formal transfer through the comparison
of Theorem 1.4.2, pp. 8–10, is not assumed or established. The action is
continuous over the fixed complete ultrametric field `K` (`Aut X`),
not one moving the base field as allowed by §1.1, pp. 1–2.

## Proposition

`Langlands.Cohomology.AnalyticGlobalSpectralSequence.AnalyticEtaleCompactSupportSpectralSequenceOnCompactBaseStatement`
uses a topological group `G`, `R`-module coefficients for one commutative
ring `R`, and the same `Small`, `HasAdmissibleRefinements`, and independent
`HasDerivedCategory` universe as the étale [ordinary statement](Statement.md).
There is no assumption that `G` is compact. It takes a normed extension
`L` of `K` with normed-algebra structure and `EtaleSite.PointAxioms L x`
for all `L`-valued points of `X`. The additional hypotheses are
`IsCompactSpace X` (compact Hausdorff) and surjectivity of
`pointProjection L X`. Supports are in the Library's `L`-valued points
with topology induced from `|X|`.

The complex `D` is the image of the actual derived smooth compact
sections `etaleGSheafCompactComplex L ρ h R` in the full derived
category. The specified sequence `spectralSequence D A` uses the
trivial smooth representation `A = trivialSmoothRep R G`. For each
sheaf `F` the proposition asserts smoothness `hs q` of the actual
`etaleRestrictionCompactCohomologyAction L ρ h R q F` on
`H^q_c(X,b^*F)` in every degree. With that action and proof of
smoothness, it asserts the additive second-page identification with
`Abelian.Ext.{w} A (SmoothRep.of _ (hs q)) p`. This is derived smooth
invariants, not a comparison with any cochain complex computing group
cohomology. It does not choose another action or assume the comparison
in Corollary 1.5.2(i).

`FirstQuadrantAbutmentStatement D A H` includes vanishing of page 2
outside the first quadrant and abutment to `H n`, the additive group
underlying `(etaleGSheafInvariantCompactCohomology L ρ h R n).obj F`,
with the finite truncation filtration and the stable-page
identifications of the ordinary model statement. These are additive
and objectwise, not asserted natural in `F` or scalar-linear.

## Intended proof ingredients

The smooth compact complex and the invariant compact abutment identify
with their ordinary counterparts on this compact base: the Library
constructions `etaleGSheafCompactComplexIsoOfCompactSpace` and
`etaleGSheafInvariantCompactCohomologyIsoOfCompactSpace` in
[AnalyticEtaleEquivariantCompactGlobal](../../Sheaf/Equivariant/AnalyticEtaleEquivariantCompactGlobal.md)
give these isomorphisms under `CompactSpace` of the underlying space and
the same point surjectivity. This reduces the abutment comparison to the
ordinary étale statement in [Statement.md](Statement.md). For the
second page, the compact comparison `etaleCompactComparison` would
identify the smooth compact cohomology with the cohomology of the
restricted sheaf, intertwining the canonical actions. Alternatively,
one can use the ordinary compact-base comparison in Theorem 1.6.1(ii)
and transport along the support-dropping isomorphisms on a compact base;
that route must check their compatibility with the restriction action.
The homology identifications and the half-bounded hyperext convergence
apply to `D` as in §1.2. No such proof, no noncompact-base version and no
quasi-étale compact-support version are supplied by this statement.
