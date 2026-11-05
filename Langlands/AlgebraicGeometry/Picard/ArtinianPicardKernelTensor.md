# Actual affine elementary Picard kernels as coefficient tensors

This internal construction works in every common universe `u`, with a
commutative base ring `k`, a field `K` over `k`, an actual scheme morphism
`f : X → Spec k`, and an elementary arrow `q : A → B` of the published
augmented local Artinian tests. The tests carry a surjective augmentation to
`K`; a section of that augmentation is not assumed. The coefficient module is
the actual ideal `Kernel q`, with its published descended residue-field action.

Write `X_A` for the actual relative scheme and `J` for the actual kernel module
of `X_B → X_A`. For every affine open `U` of `X_A`, if `f` is flat,
`affineKernelEquiv` constructs the section-ring-linear equivalence

```
(K ⊗[A] Γ(X_A, U)) ⊗[K] Kernel q ≃ₗ[Γ(X_A, U)] Γ(J, U).
```

The action of `Γ(X_A, U)` on the left comes from the right algebra action on
the inner tensor. `affineKernelEquiv_tmul` states that the underlying function
sends `(c ⊗ r) ⊗ x` to `testSectionHom f A U (c • x).val * r`.
`affineKernelEquiv_one_tmul` gives the case `c = 1`.

The implemented proof first obtains flatness of `X_A → Spec A` by base change
of `f`. The flat affine-sections theorem, composed with the canonical spectrum
sections isomorphism, proves flatness of `testSectionHom`. This equips the actual
section ring with the flat source-algebra module used by
`ElementaryKernelTensor.kernelTensorEquiv`. That published algebraic
construction identifies the tensor above with the extension of `Kernel q`.
`ArtinianSquareZeroPicardLifting.relativeMap_affine_ker` identifies that extended
ideal with the actual sectionwise kernel. Transport along this ideal equality
completes the equivalence and preserves the displayed pure-tensor formula.

`testSectionHom_res` proves that the actual source-ring map commutes with
restriction on arbitrary nested opens. `sectionRestriction` packages restriction
as an `A`-algebra map, and `fibreRestriction` tensors it with the identity of `K`.
`affineKernelEquiv_res` proves that the equivalences on two affine opens commute
with the actual restriction of `J` and the induced tensor restriction. Its proof
uses the pure-tensor formula, compatibility of the source map with restriction,
and two tensor inductions to extend the equality to all tensors.

This is an internal consequence of the actual Cartesian geometry, the affine
kernel calculation, and flat ideal tensor comparison. No properness or
cohomology premise is needed. The inner tensor is the algebraic fibre section
ring; this module does not yet construct its comparison with sections on the
actual residue fibre, a cohomology tensor comparison, a formal hull, or the
smooth Picard atlas.
