# Actual smoothing operators and compact intertwining

Author: Worker 94.

`CompactKernelAverage.smoothingLM` sends an actual derivative-topology smooth function to the scalar compact inverse-support average constructed in the preceding helpers. It is complex linear in its input. Its pointwise value is exactly the published raw convolution, and its value belongs to the closed span of the input's full actual right orbit. No compact-finiteness, center-finiteness, or analyticity premise is used.

`smoothingBilinear` makes the same operator complex linear in the actual compact smooth kernel as well. The construction uses the scalar integral's already published additivity and scalar multiplication in the kernel, followed by injectivity of the inclusion of actual smooth functions into functions. It does not require a common support for two kernels or a topology on the space of kernels.

If the kernel is invariant under conjugation by the actual whole standard compact subgroup, `smoothingLM_compactAction` proves that its smoothing operator commutes with every compact right translation. The proof uses the full-group scalar formula `∫ g, κ(g⁻¹) f(xg)`. Its integrand has compact support from the inverse kernel. Conjugation by a compact subgroup element preserves its left Haar integral by the published compact-subgroup Haar argument. The kernel's conjugation invariance and the group identities then identify the two actual smooth functions pointwise. This uses no global right invariance or inversion invariance of Haar measure.

`smoothingIntertwining` bundles that equivariance as an actual algebraic compact intertwiner. Composing with each intertwiner defining an isotypic span proves that smoothing preserves that span. Taking the finite selected supremum proves preservation of each published `selectedTypeSum`. The argument does not assert semisimplicity or a decomposition of an arbitrary compact-finite vector into types.

These are internal constructions derived from the actual scalar compact-index integration, the published raw-convolution bilinearity, compact-conjugation Haar invariance, and the published definitions of isotypic spans. All number-field universes and natural ranks, including zero, are retained. Finite-dimensional orbit-type intersections, normalized kernel approximation, exact reproduction and automorphic differential growth are separate obligations.
