# Compact manifold weighted-integral proof

Authors: Worker 116 and Worker 1659. The theorem
`Langlands.Analysis.compactManifoldWeightedIntegral` proves exactly the published
`Langlands.Analysis.CompactManifoldWeightedIntegralStatement`. It retains the six
independent universes of `X`, `V`, `M`, `H`, `N` and `E`, the original chart
structures, the original finite measure, the literal weighted integrands and the
real scalar restriction on the complete complex normed target.

## Implemented argument

`contDiffOn_compactWeightedIntegral_of_chart` treats an open parameter domain in
a real normed space when the compact integration image lies in a single chart
source. It composes the jointly smooth scalar kernel with the inverse chart,
normalizes the product model and product chart structure, then constructs the
continuous scalar family in the supremum norm. The published
`contDiffOn_infty_compactFamily_of_joint` makes that family smooth. Composition
with `compactWeightedIntegral`, restricted to real scalars, proves smoothness of
the literal weighted integral. Compact continuity separately proves integrability.

`contDiffOn_compactWeightedIntegral` removes the single-chart restriction. The
open pullbacks of the integration manifold's chart sources cover compact Hausdorff
`X`. A finite subcover and `PartitionOfUnity.exists_isSubordinate_of_locallyFinite`
give a finite continuous real partition whose topological supports lie in those
chart pullbacks. Each support is a closed compact subtype carrying the comap of
the original measure. The vector weight there is the original weight multiplied
by that partition function, and the integration map is the original continuous
map restricted to the subtype. The preceding theorem applies to each such piece.

`integral_subtype_comap` identifies each subtype integral with its restricted
integral on `X`. Its integrand vanishes outside the topological support, so
`setIntegral_eq_integral_of_forall_compl_eq_zero` identifies it with the full
integral on `X`. Integrability permits `integral_finsetSum`; the partition's
pointwise sum equal to one gives the exact finite-sum formula. Summing the smooth
pieces proves the open-domain conclusion without differentiating the partition
or the original map from `X`.

Finally `compactManifoldWeightedIntegral` works in each original parameter chart.
It composes the supplied jointly smooth kernel with the inverse extended chart
in its first variable and applies the open-domain theorem.
`contMDiffAt_iff_source` returns the result to manifold smoothness on `M`. No
finite-dimensional model, separability or smoothness of the original integration
map is used. This theorem constructs no group convolution or approximating
family and proves no smooth-vector density or automorphic tensor realization.

## Internal provenance

This is internally derived analytic infrastructure, rather than a transcription
of an external theorem. The proof combines the public compact-family calculus
in `Langlands.Analysis.CompactParameterSmoothness`, the actual bounded integral
map in `Langlands.Analysis.CompactWeightedIntegral`, and the imported Mathlib
manifold, continuous partition-of-unity and Bochner integral results. The
compact-family calculus is available through the unchanged statement module.
The proof establishes the finite chart decomposition and exact integral
identities described above using these existing results.
