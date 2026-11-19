# Faithful comparison of stabilized quotient kernels

For a faithfully flat algebra map `φ:A→B` over `R`, `rTensor_eq_zero_iff`
reflects zero under the actual right tensor extension on `A⊗_R E`. The proof
uses the canonical base-change tensor cancellation equivalence to identify
that map with `z↦1⊗_A z`, which reflects zero by faithful flatness.

`mem_map_iff` reflects membership in a classified quotient Grassmannian kernel.
The base-changed Grassmannian kernel is the kernel of the tensor extension of
the original quotient map. Evaluating on an extended vector gives the pure
tensor of its original quotient class, so faithful flatness reflects membership.

`productKernel T` is the product of the kernel of an actual first-factor linear
map with zero on a complementary module, transported through the canonical
tensor/product equivalence. `prodRight_rTensor` records exact compatibility of
that equivalence with the actual coefficient tensor map.

`productKernel_eq_classified` descends equality with a classified kernel. It
assumes that after faithfully flat coefficient extension the classified point
is the product kernel of a lifted first-factor map, and that the original map's
vanishing condition is equivalent to that of the lifted map on extended
vectors. Reflected classified membership, the product splitting identity and
reflected zero on the complement prove equality of the original submodules.

This is an internal algebraic consequence of the existing quotient
Grassmannian base-change map, tensor cancellation, product splitting and
faithfully flat module APIs. No freeness or basis choices occur. Geometric
identification of these maps with actual parabolic jet restrictions is supplied
separately in the host task.
