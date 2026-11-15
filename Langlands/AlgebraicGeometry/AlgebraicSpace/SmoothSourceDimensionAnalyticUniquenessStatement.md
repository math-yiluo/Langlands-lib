# Uniqueness of admissible varying-dimension analytic structures

Author: Worker 3519.

This derived statement is the uniqueness half of the analytic-manifold
assertion in Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
December 31, 2011, printed p.15, Proposition 5.4, for smooth spaces whose
dimension may vary. The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad asserts a unique structure with the stated properties. This unit
states that uniqueness for the Library's family-level formulation and contains
no proof.

`SmoothSourceDimensionAnalyticUniquenessStatement` is a proposition definition
in `Langlands.AlgebraicGeometry.AlgebraicSpace`. Let `K` be any nontrivially
normed field and let `Φ Ψ : DimensionAnalyticStructure K` both satisfy
`IsAdmissible`. Each choice gives a varying-dimension atlas on the original
rational points of every smooth, quasi-separated, locally separated algebraic
space over `Spec K`, with the étale-chart topology. Admissibility is the
conjunction of four conditions:

- every atlas is analytic;
- every morphism of such spaces induces an analytic map of points;
- every étale morphism induces a local analytic isomorphism that preserves
  intrinsic dimension;
- on every polynomial affine space the actual coordinate map is a bijection
  onto `Kⁿ`, analytic in both directions.

The conclusion is `Φ.Equivalent Ψ`. For every space `X` of the class, the
actual identity of `RingPoints K X K` is a `DimensionPointAtlas.AnalyticMap`
from `Φ`'s atlas to `Ψ`'s atlas and back. This includes continuity, and
analytic coordinate expressions for every pair of charts of every dimensions
on their full overlaps. It is agreement of analytic structures, not equality of
the chosen chart sets.

No completeness, henselian or nonarchimedean hypothesis is assumed. Neither
structure is assumed to arise from a pure-dimensional `AnalyticPointStructure`.
This is stronger than the published `AnalyticPointStructure.equivalent_of_isAdmissible`,
which compares pure-dimensional families only and says nothing about other
varying-dimension structures.

The intended route of a proof follows that published argument. Given a
rational point `x` of `X`, it lies in the actual dimension piece of its
intrinsic dimension `n`. That piece is smooth of pure dimension `n`, so the
published `smoothPureDimensionalAffineChart` gives an étale map from an affine
scheme smooth of relative dimension `n`, with a rational point over `x`.
Composing with the étale piece inclusion gives an étale map to `X`. Shrinking
to a standard-smooth basic open gives an étale map to affine `n`-space. The
identity is analytic in both directions on affine space by the two
normalizations. It transfers to the chart and then to a neighborhood of `x`
through the étale local analytic isomorphisms and functoriality of `Φ` and
`Ψ`. Analyticity of both atlases then gives the conclusion in every chart.

This unit does not assert existence of an admissible structure, or
admissibility of any particular structure.
