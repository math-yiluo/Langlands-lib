# Canonical factorization once the actual kernel has multiplicative type

This internal construction assembles the canonical factorization from
the proved relative multiplicative-type quotient construction and
fpqc homomorphism descent. It imports the published target without
modifying it or its dependencies.

Let `f : H ⟶ G` be a homomorphism over an arbitrary scheme `S`.
Assume `H` and the actual scheme-theoretic kernel of `f` are of
multiplicative type and `G` is separated over `S`.
`exists_factorization_of_multiplicativeType_kernel` gives an affine
actual fppf full-kernel quotient `q : H ⟶ Q`, a target `Q` of
multiplicative type, and a monomorphism `v : Q ⟶ G` with `q ≫ v = f`.
The definition `factorizationOfMultiplicativeTypeKernel` chooses this
actual data while retaining all the stated properties.

The kernel inclusion is closed because `G` is separated. Apply the
relative closed-subgroup quotient theorem to this inclusion. The
affine projection is quasi-compact, so the existing full-kernel
fpqc factorization helper supplies its monomorphic factor to `G`.
No finiteness condition on `G` or Noetherian condition on `S` is needed
after multiplicative type of the kernel has been supplied.

The final theorem,
`multiplicativeTypeKernelFactorization_of_kernelCriterion`, reduces the
unchanged published `MultiplicativeTypeKernelFactorizationStatement`
to its kernel-multiplicative-type clause under exactly its original
separation and finiteness alternatives. That kernel criterion remains
an explicit premise of this reduction. The module does not claim an
unconditional proof of the published target.
