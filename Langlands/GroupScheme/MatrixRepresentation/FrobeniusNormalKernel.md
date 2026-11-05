# Exact normal kernels in positive characteristic

Work over an algebraically closed field `k : Type u` of exponential
characteristic `p`, with `p.Prime`. Let `G` be affine and locally of finite
type over `Spec k`, and let `i : H ⟶ G` be a closed subgroup whose range is
normal. Neither `G` nor `H` is assumed reduced, smooth or connected.

`nonempty_kernelRepresentation_of_prime_expChar` constructs an actual finite
matrix representation with full kernel range equal to the range of `i`.
`normalKernelRepresentationOfPrimeExpChar` chooses that representation in the
existing `KernelRepresentation i` package. The theorem
`exists_normal_kernel_of_prime_expChar` exposes its dimension, actual group
scheme homomorphism into the general linear group, and exact kernel equality.
The kernel is the actual pullback kernel, and the equality of subgroup functors
holds on every relative scheme test, including nonreduced tests.

The implemented proof first obtains the subgroup's affineness and the required
monomorphism from its closed immersion into `G`. The previously constructed
Frobenius character argument supplies `HasInverseMultipleNormalCharacters i`:
each occurring subgroup character has the inverse of a positive `p`-power
multiple in an actual ambient representation. The previously constructed
Chevalley and positive tensor construction then gives the exact kernel.
Choice and projection of its fields give the two remaining declarations.

This is an internal assembly of the character and tensor constructions motivated
by Milne, *Algebraic Groups* (2017), Lemmas 5.16–5.17, printed pp. 102–103
(PDF pp. 118–119). Its positive-characteristic character input uses nilpotent
coordinate defects rather than constructing a smooth Frobenius image. The
tensor input uses ambient representations as required by the official erratum
to Corollary 4.29, printed p. 95. This unit proves the algebraically closed
positive-characteristic exact-kernel result; characteristic zero, descent to
arbitrary fields, and existence of a faithfully flat quotient remain separate
obligations of the general quotient theorem.
