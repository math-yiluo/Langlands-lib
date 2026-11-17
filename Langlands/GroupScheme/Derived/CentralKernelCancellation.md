# Cancellation through central kernels for perfect source groups

`centralKernelDifference` upgrades the existing scheme morphism
`kernelDifference q a b hab` to a homomorphism `C ⟶ kernel q` whenever
`a b : C ⟶ H` satisfy `a ≫ q = b ≫ q` and the full kernel of `q : H ⟶ G`
is central. Its composite with the kernel inclusion is the quotient of
the two underlying maps. This construction works over any base scheme.

The auxiliary `kernelDifference_isMonHom` checks multiplicativity on all
generalized points. Each quotient of two corresponding points lies in the
central kernel. Commuting that quotient past the other factor proves the
multiplication law. `centralKernelDifference_comp` records the underlying
quotient identity.

`centralKernel_cancel_of_perfect` shows that `a = b` if additionally the
full derived subgroup of `C` is all of `C` and the kernel is separated over
the base. Centrality makes the kernel commutative. Every homomorphism from
the perfect source to this separated commutative kernel is trivial by
`IsDerivedSubgroup.comp_eq_one`; hence the difference is trivial.

`IsCentral.kernel_baseChange` transports centrality of an actual kernel
through the canonical kernel/base-change isomorphism.
`derivedSubgroup_eq_top_baseChange` uses the published arbitrary-affine
base-change theorem for derived subgroups to preserve perfectness of an
affine group over a field. In particular,
`IsSemisimple.centralKernel_cancel_baseChange` applies cancellation to a
semisimple field group after every affine base change. This includes
nonreduced scalar-extension algebras, as needed on descent overlaps.
The base-changed kernel must be separated; no smoothness of it is assumed.

## Provenance

This is an internal derived construction and its supporting theorems.
Its inputs are the published `kernelDifference` construction, pointwise
centrality, derived-subgroup annihilation of separated commutative
targets, arbitrary-affine derived base change, and semisimple perfectness.
The proof route is the direct pointwise quotient argument described above.
No multiplicative-type rigidity assertion is introduced here.
