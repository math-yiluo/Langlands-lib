# Unipotent kernel coverage by an open binary cell

This internal construction works over an arbitrary field. It supplies an actual
factorization of the full scheme-theoretic ambient kernel through a compatible
open binary multiplication cell.

First, `isIso_cellMultiplication_of_unipotent_overField` extends the published
algebraically closed field criterion to the original field: smooth affine
unipotent factors whose multiplication is an open immersion into a connected
affine locally finite-type group cover that group. The proof extends scalars
to the algebraic closure. The canonical comparison of products identifies the
extended multiplication; connectedness and unipotence persist under extension,
so the algebraically closed criterion gives surjectivity. Scheme surjectivity
reflects along the surjective field extension. The original open immersion is
therefore an isomorphism.

For the kernel application, use compatible homomorphisms `q : G → H`,
`f : U → V`, `g : P → R` and source and target inclusions as in `KernelCell`.
Assume the source inclusions are closed, `U` and `P` are affine, `V` and `R`
are separated, and `f` and `g` are smooth. Assume the full kernel of `q` is
affine, locally of finite type, connected, and unipotent. The source
multiplication is an open immersion and the target multiplication is monic.

`isClosedSubgroup_kernelHom` proves that each induced kernel inclusion is
closed by composing it with the monic ambient kernel inclusion and cancelling
closedness from that composite along the separated monomorphism. Each factor kernel is smooth by its actual
pullback square and affine by its closed inclusion into the original affine
factor. Published inheritance of unipotence by closed subgroups makes both
factor kernels unipotent. The cartesian square from `KernelCell` makes their
multiplication an open immersion. The preceding original-field criterion
then constructs `unipotentKernelCellIso`.

`kernelChart` is its inverse followed by the two original kernel inclusions.
`kernelChart_comp` states that its composite with the original cell is exactly
the full kernel inclusion, on every test scheme and over the original field.
No existence of quotient maps, dynamic representatives, radicals or integral
opposite factors is asserted.

The provenance is internal composition of the actual kernel construction,
the compatible-cell pullback, closed-subgroup unipotence, algebraic-closure
base change, and descent of surjectivity. This is a supporting unit for
Task 6404, not the proof of its depth-zero opposite-factor statement.
