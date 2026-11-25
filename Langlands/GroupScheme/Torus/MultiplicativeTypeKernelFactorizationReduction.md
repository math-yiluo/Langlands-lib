# The exact canonical factorization from the two rigidity inputs

Internal conditional assembly toward the canonical factorization of
homomorphisms from groups of multiplicative type.

`multiplicativeTypeKernelFactorization_of_rigidity_and_spreading` has type
`MultiplicativeTypeKernelFactorizationStatement` with two explicit
premises: proofs of the exact
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
criterion and the factorization constructor
`factorizationOfMultiplicativeTypeKernel` (module
`MultiplicativeTypeFactorizationFromKernel`).

The imported helper constructions (modules
`MultiplicativeTypeKernelRigidityReduction` and
`MultiplicativeTypeFactorizationFromKernel`) are derived content assembled
from the Library constructions and stated explicit premises. Neither rigidity
nor monomorphism spreading is proved here; consequently this module
is not an unconditional proof of
`MultiplicativeTypeKernelFactorizationStatement`. The unconditional proof is
`multiplicativeTypeKernelFactorization` in
`MultiplicativeTypeKernelFactorizationProof`.
