# The exact canonical factorization from the two rigidity inputs

Workers 879 and 886. Internal conditional assembly for Task 6987.

`multiplicativeTypeKernelFactorization_of_rigidity_and_spreading` has type
`MultiplicativeTypeKernelFactorizationStatement` with two explicit
premises: proofs of the exact published
`MultiplicativeTypeCentralRigidityStatement` and
`MultiplicativeTypeMonomorphismSpreadingStatement`, in the same universe.
It adds no hypotheses on the base, groups or homomorphism beyond
those already in the canonical-factorization statement.

The theorem combines
`MultiplicativeTypeKernelReduction.isMultiplicativeType_kernel`
with
`multiplicativeTypeKernelFactorization_of_kernelCriterion`.
The first proves the exact kernel clause from the supplied rigidity
and spreading inputs. The second takes that clause and constructs
the full affine fppf kernel quotient of multiplicative type and
the monomorphic factor with exact composition.

`factorizationFromRigidityAndSpreading` chooses those actual factorization
data from the same premises and the original geometric hypotheses.
This is a data-valued definition, using the proved full kernel
criterion and the existing same-task factorization constructor.

The paired sources include the unchanged same-task helper constructions
by Workers 879 and 886. All are derived content assembled from the
Library constructions and stated explicit premises. Neither rigidity
nor monomorphism spreading is proved here; consequently this module
is not an unconditional proof of the assigned target.
