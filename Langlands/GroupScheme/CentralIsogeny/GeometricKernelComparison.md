# Comparison of isogenies by geometric kernel cardinalities

`GeometricKernelCardComparisonStatement` concerns a factorization `a ≫ r = p` of actual group-scheme homomorphisms over a characteristic-zero field, where `a` is an isogeny. If the scheme kernels of `p` and `r` have the same positive finite number of points over an algebraically closed coefficient field, then `a` is an isomorphism.

`IsIsogeny.isIso_of_geometricKernel_card_eq` proves the assertion. Every point of the geometric kernel of `r` lifts through `a`, and its lift belongs to the geometric kernel of `p`. Equality of the finite cardinalities makes this surjection injective and forces the geometric kernel of `a` to have only its identity point. The finite actual kernel is smooth by Cartier's theorem. Over the algebraically closed coefficient field its closed points are rational and dense, so it is a reduced singleton. Descent identifies the kernel with the base, and the original finite faithfully flat monomorphism is an isomorphism.

`exists_iso_centralCover_of_geometricKernel_card_eq` applies the criterion to two central covers of the same semisimple group. One source is simply connected and the other is semisimple. The common semisimple refinement has an invertible map to the simply connected source, leaving an isogeny between the two covers to which the cardinality criterion applies.

The criterion is derived from the Library's full scheme kernels, algebraically closed point lifting, Cartier smoothness, and descent for reduced geometric singletons. It supplies the comparison between central double covers used in the scalar spin Hasse argument of Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.11, p. 99.
