# Naturality of square-zero reduction kernels

Namespace `Langlands.GroupScheme.Lie.NonaffineKernel`. Let
`G : GroupScheme (Spec R)` be arbitrary. Take an `R`-algebra map
`f : A →ₐ[R] B`, an ideal `J` of `A`, and an ideal `J'` of `B` with
`J.map f ≤ J'`.

- `reduction_affineMap`: reducing after `f` is the same as reducing first
  and then applying the induced quotient map `Ideal.quotientMapₐ`.
- `kernelMap G J f h : kernel G J →* kernel G J'` is the restriction of
  `Lie.affineMap G f`. `kernelMap_left` records that its underlying
  morphism is `Spec.map f ≫ x.left`.
- `kernelMapAdd` is the additive version.
- `kernelMap_smul`: if `J` and `J'` are square-zero (as `Fact`
  instances), then `kernelMapAdd G J f h (a • x) = f a • kernelMapAdd G J f h x`
  for the module structures of `NonaffineKernel`.

The proof of `kernelMap_smul` has three steps:
1. Restriction from `A` to `B` commutes with global affine combinations
   (`SmoothLifting.gcomb_res`).
2. The combination for the base-changed data agrees with the combination
   for the data of the kernel modulo `J'` (`SmoothLifting.gcomb_data_indep`).
3. Restricting the identity gives the identity.

These are internal constructions for the lifting of homomorphisms from
groups of multiplicative type through nilpotent thickenings; they give
naturality of coefficients along test algebras.
