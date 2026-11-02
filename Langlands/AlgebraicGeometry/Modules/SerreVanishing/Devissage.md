# Two-bundle vanishing by induction on actual support

This internal unit reduces the two-ample-bundle vanishing assertion to the explicit
`SectionKillingStatement` premise. `GoodInSupportDimension f L1 L2 e` says that
every quasi-coherent coefficient with finite affine sections and actual support
bound `e` satisfies `Good` for the two line bundles. All schemes, fields and
coefficients retain the arbitrary universe of the target.

The induction starts at bound zero, where the coefficient is zero. For the
successor step, the existing coherent integral-ideal filtration expresses the
coefficient as a finite sequence of extensions of pushforwards of nonzero
coherent ideals on integral closed subschemes. Each factor inherits the endpoint's
support bound. The actual closed support of such a factor is the irreducible
closed image of its integral subscheme: the ideal has full closed support, and
closed pushforward takes support to its image. Its height is therefore at most
`e` when the factor has bound `e + 1`.

For each ample line bundle, the Support module supplies a section in a positive
power with affine trivialization locus meeting this irreducible support. Both
multiplication kernels and cokernels have bound `e`; they are coherent by the
existing kernel, cokernel and rank-one tensor closure facts. Applying the
induction hypothesis to the four errors and then `Good.of_sectionKilling` gives
`Good` for the factor. `Good.filtration` and the endpoint isomorphism give the
result for the original coefficient.

The Lean proof uses the existing unconditional integral-ideal filtration theorem.
The section-killing premise remains explicit. This module does not assert an
unconditional proof of Serre vanishing, nor does it assert a finite global
dimension bound for a proper scheme. Its provenance is the derived support
induction and categorical extension argument for the authorized target task.
