# Integral coordinates adapted to an actual valuation kernel

This derived unit supplies product coordinates for the actual valuation-image
map of a morphism of connected reductive groups over a nonarchimedean local
field. The map and its kernel are the ones used by actual unramified character
restriction; no abstract replacement lattice is assumed.

`integerMap` gives the additive integer-linear form of the existing map, and
`kernelEquiv` identifies its kernel with the additive form of the original
multiplicative kernel. The image is a submodule of a finite free integer module,
so it is finite free and projective. A linear section of the range restriction therefore
gives a projection onto the kernel. This proves `actual_exists_isCompl_ker`.

`exists_product_coordinates` chooses finite integer bases of the kernel and
its complement and transports the direct-sum equivalence to a product of
finite coordinate lattices. Vanishing of the second block is equivalent to
membership in the original valuation kernel. The kernel is the first block,
and its rank is not presumed to be positive.

`kernel_finrank_le_one` proves that a cyclic valuation kernel has integer rank
at most one. `exists_maximalLevi_product_coordinates` combines this with
`maximalLevi_rationalValuationKernel_isCyclic` to leave zero or one kernel
coordinates for an actual maximal proper Levi. These are structural coordinate
statements, not a rational scalar descent or regularity theorem.
