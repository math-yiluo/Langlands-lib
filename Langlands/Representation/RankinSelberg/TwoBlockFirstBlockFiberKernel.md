# The first-block slice fiber kernel

Author: Worker 27.

This internal module constructs the actual measurable fiber kernel for the
published first-block quotient data. Given an s-finite measure `νA` on
`N_a \ GL_a` with the published `NormOneRightInvariant` property, its
`fiberKernel F h νA hνA k` has value at every representative `g` equal to the
pushforward of `νA` restricted to the small determinant slice `k` under
`q ↦ fiberPoint h F.Carrier q g`. No factor or additional normalization is
introduced.

The proof first restricts right-translation invariance to each determinant
slice. The published formula `fiberPoint_mixedEmbedding_mul` then proves
invariance of these measures under changing a representative by left
multiplication from the mixed subgroup. The kernel is the actual quotient
descent of that invariant map into the space of measures. Joint continuity
of the fiber map and s-finiteness of the restricted small measure prove
measurability before descent. The published Borel quotient measurability
criterion proves measurability after descent.

This is derived measure-theoretic packaging for JPSS (1983), Section 4.6,
printed page 412, equation (6), using the already published actual groups,
quotients and fiber map. This module proves neither s-finiteness of the
kernel nor a disintegration identity; these are separate proof obligations.
