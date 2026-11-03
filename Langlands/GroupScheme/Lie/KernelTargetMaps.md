# Homomorphisms on actual dual-number identity kernels

This internal module collects the actual tangent map of a group-scheme
homomorphism over `Spec R`, uniformly in the universe and coefficient algebra.
It uses the published dual-number identity kernel and epsilon-scaling module
structure from `Lie.AffineModule`.

`Lie.targetMap f A` sends a kernel point to its composite with `f`.
`Lie.targetMapLinear f A` bundles the same map as an A-linear map for affine
source and target. These are the existing constructions formerly in
`Rational.SplitTorusFiniteRank`, moved here with their names, types and bodies
unchanged. The duplicate constructions submitted as `lieKernelTarget` and
`lieKernelTargetLinear` are replaced by these canonical declarations.
`Lie.targetMapLinear_injective` retains injectivity for monomorphisms.

The existing reduction, evaluation, coefficient-change, epsilon-scaling and
injectivity lemmas are collected from `Dynamic.ParabolicLieCriterion`,
`Rational.ActionWeightTransport`, `Rational.TangentImage` and
`Rational.TangentWeightTransport`. Their public names and explicit or implicit
argument conventions are unchanged. In particular, `Lie.reduction_comp_hom`,
`lieKernelTarget_val`, `lieKernelTarget_map`, `lieKernelTarget_scale`,
`lieKernelTarget_injective`, `lieKernelTargetLinear_toMul` and
`lieKernelTargetLinear_val` describe the same actual postcomposition map.
The old modules import this common module and retain their other results.

The new `Lie.mem_lieKernel_comp_hom_iff` packages preservation and reflection
of reduction to the identity under a monomorphism. Reflection cancels the
underlying scheme map; it needs no affineness, smoothness or field hypothesis.
The new `lieKernelTargetLinear_map` states compatibility of the linear map
with semilinear coefficient change, by the same pointwise composition identity.

The provenance is internal: these results follow from point composition,
the published kernel and module constructions, and categorical cancellation.
They assert no geometric realization, Lie bracket compatibility or cyclic-root
comparison.
