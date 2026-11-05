# Quotienting an elementary Artinian test by a residue-kernel subspace

Fix commutative `k`, a field `K` with its `k`-algebra structure, actual augmented
Artinian tests `A` and `B`, and an elementary arrow `q : A ⟶ B`. All rings and
tests lie in an arbitrary common universe `u`. The premise is supplied as
`Fact (IsElementarySurjection q)` so the local module instance can recover it.
Write `J` for the actual ideal kernel of the underlying algebra map. Use the
canonical `ElementaryKernel.residueModule` on `J`, obtained by descending its
source-ring action through the specified surjective augmentation `A → K`.
No coefficient-field section or `K`-algebra structure on `A` is required.

For every `K`-subspace `W` of `J`, `subspaceIdeal` is its image under `J ↪ A`.
Closure under multiplication follows from `augmentation_smul`: multiplication
by `a : A` on `J` is scalar multiplication by its residue in `K`. The lemma
`mem_subspaceIdeal` identifies membership of actual kernel elements with
membership in `W`. This ideal lies in `J`, hence in the augmentation kernel,
and is annihilated by the source maximal ideal.

The actual test `test q W` has underlying ring `A / subspaceIdeal q W` and the
augmentation descended from the original augmentation of `A`. The map
`projection q W` is the ordinary quotient map. The map `reduction q W` is
the ordinary quotient lift of `q`, and `projection_reduction` proves their
composite is exactly `q`. The projection is elementary because its kernel
is `subspaceIdeal q W`, which the maximal ideal annihilates. The reduction
is surjective, and `ker_reduction` identifies its actual kernel with the
image of `J` in the quotient. The quotient maximal ideal is the image of
the source maximal ideal, so preservation of ideal products proves that
the reduction is elementary as well. Zero subspaces, whole kernels, and
zero-dimensional kernels are permitted.

The additive map `kernelMap q W` sends an actual kernel element to its
ordinary quotient class in the actual kernel of the reduction. It is
surjective: any quotient class in the latter kernel has a representative
in `A`, and that representative lies in `J`. Give the new kernel its
canonical residue action for `reduction_elementary`. The construction
`kernelLinearMap q W` proves this same additive map is `K`-linear. To check
linearity, lift each scalar through `A → K`, use the augmentation triangle
and `augmentation_smul` on both kernels, and apply multiplicativity of
the ordinary quotient map.

The lemma `ker_kernelLinearMap` says its kernel is exactly `W`. The first
isomorphism theorem therefore gives the actual linear equivalence
`quotientKernelEquiv q W : (J / W) ≃ₗ[K] Kernel (reduction q W)`.
The equation `quotientKernelEquiv_mk` identifies its value on every quotient
representative with `kernelMap`, so the equivalence retains the specified
quotient map rather than merely comparing dimensions.

This is an internal construction from the existing augmented Artinian-test,
elementary-kernel, quotient-ideal, and linear first-isomorphism infrastructure.
The paired Lean implements the ideal-product and representative arguments
above. It supplies the algebraic quotient used when selecting kernel
coefficients. It makes no assertion that a Picard obstruction has been killed,
and supplies no formal family, hull, versality, or smooth atlas.
