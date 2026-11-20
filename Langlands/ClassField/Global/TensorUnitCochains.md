# Primitives and finite refinements of tensor-unit cochains

`tensorCoboundary` and `tensorDifferential` are the crossed differentials on
the units of the actual tensor algebra `B ⊗[F] L`, with automorphisms of `L/F`
acting on the right factor. Scalar extension on this factor commutes with
restriction of automorphisms when `L/F` is normal. The degree-two
differential of a tensor-unit coboundary is one.

For finite separable `B/F` embedded in a finite Galois extension `L/F`,
Shapiro identifies degree-one tensor-unit cohomology with unit cohomology
over `B`. Finite relative Hilbert 90 over `B` then gives an actual
radical for every crossed tensor-unit cocycle. To take an `n`-th root
of a tensor unit in characteristic zero with `n > 0`, split the finite
family of radical polynomials for its embedding coordinates. Take a
finite Galois closure over `F` and use the tensor product decomposition
to assemble the resulting coordinate radicals into one tensor unit.

`TensorTorsionPrimitiveAfterRefinement` asks for a primitive of a given
crossed degree-two cochain after a finite Galois refinement, with
`n`-th power one in every value of the primitive. The companion theorem
starts with a tensor-unit primitive whose degree-two differential has
`n`-th power one. The `n`-th power of the primitive is then a crossed
cocycle. Express it as the coboundary of a tensor unit by Hilbert 90
and take an `n`-th root of that unit on a refinement. Dividing the
original primitive by the coboundary of that root preserves the
degree-two differential and makes every value have `n`-th power one.
This is an internal calculation for the norm-kernel obstruction.
