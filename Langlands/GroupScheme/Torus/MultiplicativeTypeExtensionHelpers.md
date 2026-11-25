# Reductions for extensions of multiplicative-type groups

Internal reductions toward `MultiplicativeTypeFieldExtensionStatement`.

These internal lemmas reduce parts of the fixed field-extension target to
geometric descent and to vanishing of maps to the additive group. They do not
prove the target; it is proved as `multiplicativeTypeFieldExtension` in
[`MultiplicativeTypeFieldExtensionProof`](MultiplicativeTypeFieldExtensionProof.md),
which imports this module.

The quotient pullback is the product of the source with its represented kernel.
Affineness of the kernel makes its first projection affine. Descent of affine
morphisms along the given fppf cover then makes the quotient projection affine;
quasi-compactness is a consequence rather than an additional hypothesis. An affine
finite-type target consequently gives an affine finite-type source, because the
quotient projection is already locally of finite presentation.

A homomorphism killing the represented kernel kills the full scheme kernel,
using their isomorphism on all test schemes. The published fpqc homomorphism
descent theorem factors it through the quotient. The construction
`RelativeRoot.IsFppfQuotient.quotientHomEquiv` packages this factorization
as an equivalence between actual homomorphisms out of the quotient and
actual homomorphisms out of the middle group killing the represented kernel.
Its inverse laws are the factorization and uniqueness lemmas of fpqc descent. If both outer groups have
only the zero homomorphism to a fixed group, so does the extension.

Finally, a homomorphism from an arbitrary diagonalizable group to the additive
group is zero. For each affine test algebra, translate the universal diagonalizable
point by the given constant point. Its additive image is the sum of the universal
image and the constant image. Taking the degree-zero group-algebra coefficient
is invariant under translation and recovers the constant image, which is
therefore zero. Affine-test extensionality proves equality of actual group-scheme
homomorphisms. No finite-generation or smoothness condition is used in this step.

These are derived consequences of the imported Library constructions, in
particular `QuotientCell.multiplication_isPullback`,
`RelativeRoot.IsFppfQuotient.kernelIso`, `FpqcHomDescent`, and
`DiagonalizableAverage`.
