# Realizing a supplied labeling of an actual integral word

Authors: Worker 320 (proof and original draft), Worker 495 (verification
and submission).

The degree helper `integralCuspidalJacquetWord_length_mul` proves that the
word length times the fixed supercuspidal rank equals the ambient rank.
The rank-indexed class equalities identify each actual block size with that
fixed rank, and the block shape's sum identity gives the result. Repeated
labels remain separate blocks.

This internal helper starts with a realized integral cuspidal Jacquet word
and a supplied ordered family of actual supercuspidal objects whose integer
labels give that same word on the same fixed twist line. It proves that the
supplied family's actual external tensor occurs in the normalized upper
Jacquet module for its supplied block shape.

The chosen witnesses of the realized word have the same number of blocks
as the supplied family. Every block rank equals the fixed line's rank,
by the dependent rank-indexed class equalities. Thus the two ordered block
shapes agree. Injectivity of `List.ofFn` identifies their label functions.
Their block classes agree pointwise, hence their actual supercuspidal
objects are isomorphic. The finite external tensor functor carries these
isomorphisms to an isomorphism of the actual tensors, which transports the
subquotient occurrence.

This is internal reasoning about the existing actual-word definition,
equality of ordered shapes, and actual tensor isomorphisms. It imposes no
irreducibility, admissibility, finite length, or analytic hypothesis on the
ambient representation. It does not replace a subquotient occurrence by a
whole Jacquet quotient or induction embedding.
