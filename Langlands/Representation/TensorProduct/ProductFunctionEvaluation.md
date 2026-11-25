# Evaluation on a product of domains

Suppose each coefficient space maps linearly to scalar functions on its
own domain. A pure tensor evaluates on a tuple of arguments by multiplying
the corresponding function values. Multilinearity extends this evaluation
to the tensor product.

Point evaluations span the algebraic dual of a finite-dimensional
coefficient space embedded in functions. A basis of point evaluations
identifies the space with functions on a finite sample. Tensoring these
identifications and using Mathlib's tensor product of finitely supported
functions identifies the finite tensor product by its values on the
product of the samples.

If every slice in a coordinate belongs to one fixed finite-dimensional
space of functions, the values on the product of the samples determine
the whole function. Releasing one coordinate at a time reduces this
claim to injectivity of the sample evaluations in that coordinate. The
tensor determined by the sample values has its slices in the same
coefficient spaces.

Every algebraic tensor belongs to the image of a tensor product of
finite-dimensional subspaces, obtained by collecting its finitely many
pure tensor factors. This gives injectivity of product evaluation when
each coefficient map is injective, including for infinite-dimensional
coefficient spaces. The construction is used to identify the
cuspidal Levi coefficients with actual tensors in the proof of
`CuspidalSupportExistenceStatement` (every automorphic representation of
GL_n is a constituent of a cuspidally induced representation at the finite
places), in `Langlands.Global.Factors.CuspidalSupportExistenceProof`.
