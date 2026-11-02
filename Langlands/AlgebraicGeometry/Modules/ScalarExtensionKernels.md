# Kernel coefficients after extending a field

This internal linear-algebra construction uses Mathlib's exactness of tensoring
with a flat module. A field extension is flat because its underlying module is
a vector space. `scalarKernelImage` is the image of the scalar-extended kernel
in the extended source of a linear map. Its membership criterion is exactly
vanishing under the scalar-extended map.

`exists_kernel_coefficient_of_ne_zero` considers an element of this kernel and
two further linear maps. If their composite is nonzero on that element, then it
is nonzero on the image of `1 ⊗ s` for some actual vector `s` of the original
kernel. The proof lifts through tensor exactness and uses tensor-product
induction: if every such vector had zero image, every pure tensor, and hence
every finite sum, would have zero image. No choice of a basis or separability
assumption is used. This is an internal coefficient extraction lemma and does
not by itself prove a geometric descent or ampleness claim.
