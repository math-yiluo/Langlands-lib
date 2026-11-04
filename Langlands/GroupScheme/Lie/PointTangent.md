# The actual Lie kernel and the tangent module at the identity

This internal construction compares two existing descriptions of the tangent
space of a group scheme over a field. Let `k : Type u` be any field and let
`G` be a group scheme over `Spec k`. Write `e` for its identity section and
`R` for the stalk of its structure sheaf at the image of the unique point of
`Spec k` under `e`.

`Lie.kernelTangentEquiv` identifies the actual identity kernel
`lieKernel G k` with scheme morphisms `Spec (DualNumber k) → G` that are over
`Spec k` and restrict to `e` on the closed point. This set equivalence does
not require affineness or finite type. Its forward map forgets the slice
structure on a kernel point; its inverse restores that structure using the
first tangent-vector equation. The second tangent-vector equation is exactly
the kernel's reduction-to-identity equation. The identity points used by the
two interfaces have the same underlying scheme morphism.

`Lie.kernelStalkDerivationEquiv` then identifies this kernel with the
`k`-derivations `R → k`. The base algebra on `R` is the published
`Picard.stalkAlgebraOver`; the coefficient action of `R` on `k` is through
`Picard.rationalStalkAugmentation` at `e`. This is the composite of the
preceding equivalence and the inverse of the existing
`Picard.rationalStalkDerivationTangentEquiv`.

When the structure morphism of `G` is affine,
`Lie.stalkDerivationKernelLinearEquiv` upgrades the inverse comparison to a
`k`-linear equivalence from these stalk derivations to
`Additive (lieKernel G k)`. Addition on this last module is the original
multiplication of identity-kernel points, and scalar multiplication is
precomposition by the dual-number map that multiplies epsilon by the scalar.
The addition proof is the published
`Picard.rationalStalkDerivationPoint_add` for the group object `G.X`.
The scalar proof is the published
`Picard.rationalStalkDerivationTangentEquiv_smul`; the epsilon-scaling ring
maps of the two interfaces agree. Local specialized instances use exactly
the existing commutative-group, scalar-action and module structures on the
Lie kernel.

`Lie.kernelPointTangentLinearEquiv` gives the resulting linear equivalence

```
Additive (lieKernel G k) ≃ₗ[k] Langlands.Scheme.tangentSpaceAtPoint G.X e.
```

It composes the inverse of the preceding comparison with the inverse of the
published `Picard.tangentSpaceAtPointDerivationEquiv`. Thus it compares the
original dual-number kernel with the existing tangent module, without
introducing a substitute definition of the Lie space.

If `G` is also locally of finite type over `k`,
`Lie.finrank_kernel_eq_cotangent` proves that its actual Lie finrank equals
`Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)`.
This follows by invariance of finrank under the displayed linear equivalence
and the published `Langlands.Scheme.fieldPointTangentLocalRegularity`.

The provenance is internal: the module assembles the cited published
actual-point and stalk-derivation interfaces and transfers their dimension
comparison. There is no smoothness, connectedness, reductivity, separability
or characteristic premise. This unit does not identify cotangent dimension
with Krull dimension, prove dimension invariance under isogenies, or prove
the central-isogeny root-datum statement; those remain further steps.
