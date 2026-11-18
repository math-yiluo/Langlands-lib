# Full star orbit weights and the actual anisotropic kernel

Author: Worker 5662.

This module computes the restriction of full-star orbit weights to the
absolute torus of an anisotropic kernel. The kernel is any group `D` with
index data `e` and a published `TitsIndexData.KernelComparison h` with the
index data `d` of `G`. The restriction is
`KernelComparison.weightRestriction`, actual character precomposition with
the base-changed torus morphism of the comparison. The orbit weight
`d.absoluteOrbitWeight hsc a` is the sum of the actual integral fundamental
weights over the finite full-star orbit `d.starOrbitVertices a`, each vertex
counted once.

## Exhaustive orbit dichotomy

`mem_zeroVertices_of_mem_starOrbitVertices` shows that a vertex in the
orbit of `a` is a zero vertex exactly when `a` is one. It uses the published
full star invariance of the zero vertices, `titsIndexStarInvariant`.
`starOrbitVertices_subset_zero_or_disjoint` concludes that every full star
orbit lies in the zero vertices or is disjoint from them. No index
admissibility premise is used.

## Orbits inside the zero vertices

`KernelComparison.mem_starOrbitVertices_vertexEquiv_iff` and
`KernelComparison.exists_of_mem_starOrbitVertices` show that the actual
vertex equivalence `h.vertexEquiv : e.Vertex ≃ d.zeroVertices` maps the full
star orbit of a kernel vertex `c` onto the full star orbit of
`h.vertexEquiv c`. This uses the published `KernelComparison.vertexEquiv_star`.

The fundamental weight at the zero vertex `h.vertexEquiv c` restricts to
the fundamental weight at `c`
(`KernelComparison.weightRestriction_absoluteFundamentalCharacter_vertexEquiv`).
Reindexing the orbit sum by the vertex equivalence gives
`KernelComparison.weightRestriction_absoluteOrbitWeight_vertexEquiv`:

`h.weightRestriction (d.absoluteOrbitWeight hsc (h.vertexEquiv c)) =
  e.absoluteOrbitWeight hscD c`.

`KernelComparison.weightRestriction_absoluteOrbitWeight_of_zero` states the
same formula indexed by an ambient zero vertex `a`. The kernel vertex is
`h.vertexEquiv.symm a`.

## Orbits outside the zero vertices

If `a` is not a zero vertex, every vertex of its orbit is distinguished. The
fundamental weight at a distinguished vertex restricts to zero
(`KernelComparison.weightRestriction_absoluteFundamentalCharacter_distinguished`), so
`KernelComparison.weightRestriction_absoluteOrbitWeight_of_not_zero` gives
`h.weightRestriction (d.absoluteOrbitWeight hsc a) = 0`.

`KernelComparison.weightRestriction_absoluteOrbitWeight_cases` combines both
cases. For every ambient vertex `a`, one of the following holds. The orbit
lies in the zero vertices, `a = h.vertexEquiv c` for some kernel vertex `c`,
and the restriction is `e.absoluteOrbitWeight hscD c`. Otherwise the orbit is
disjoint from the zero vertices and the restriction is zero.

`KernelComparison.restrictedOrbitWeight h hscD a` is the explicit value. If
`a` is a zero vertex, it is `e.absoluteOrbitWeight hscD (h.vertexEquiv.symm a)`.
Otherwise it is `0`. `KernelComparison.weightRestriction_absoluteOrbitWeight`
proves `h.weightRestriction (d.absoluteOrbitWeight hsc a) =
h.restrictedOrbitWeight hscD a` for every ambient vertex `a`.

The general statements take simple connectedness of both `G` and `D` as
hypotheses. These give the integral fundamental-weight bases through the
Library theorem `TitsIndexData.pinning_corootSpan_eq_top`.

## The chosen actual anisotropic kernel

For `p : d.AnisotropicKernelIndex`, the restriction map
`AnisotropicKernelIndex.weightRestriction p` of `p.comparison` is defined in
`SimplyConnected/AnisotropicKernelStarRestriction`. Here `p.kernel` is the
actual derived subgroup of an actual representative of the centralizer of the
maximal split torus. The Library theorem
`AnisotropicKernelIndex.isSimplyConnected` proves that `p.kernel` is simply
connected when `G` is. The definition
`AnisotropicKernelIndex.restrictedOrbitWeight p hsc a` is
`p.comparison.restrictedOrbitWeight` for this kernel.
`AnisotropicKernelIndex.weightRestriction_absoluteOrbitWeight` identifies it
with the restriction of the orbit weight. The specializations
`AnisotropicKernelIndex.weightRestriction_absoluteOrbitWeight_of_zero` and
`AnisotropicKernelIndex.weightRestriction_absoluteOrbitWeight_of_not_zero`
give the two orbit formulas. All of these need only `IsSimplyConnected G`.

All statements hold over every field and in every characteristic. No
rank-one, local-field, inner-type or star-triviality hypothesis is used.

The provenance is internal: the module combines published kernel-comparison,
star-invariance and orbit-weight results by finite reindexing. It concerns
characters only. It constructs no Tits obstruction and proves no equality of
Brauer classes; that comparison is a separate result.
