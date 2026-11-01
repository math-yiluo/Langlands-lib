# The actual zero-section unit kernel

Let `k : Type u` be an arbitrary field, let `X : Scheme.{u}`, and let
`f : X ⟶ Spec k`. Use the actual pullback `thickening f`, its first projection
`projection f`, and the actual zero section `closedPoint f` from
`DualNumberThickening`.

For every open `U` of `X`, `reductionMap f U` is the actual ring map

```
Γ(thickening f, projection f ⁻¹ᵁ U) → Γ(X, U)
```

induced by the zero section, using `Scheme.Hom.appLE`. The equality of the
composite zero section and projection with the identity supplies the inclusion
of opens in this construction. `projection_reductionMap` proves that this map
retracts the actual first-projection section map.

`testSectionMap_reductionMap` proves that the constant dual-number section map,
followed by reduction, is the usual field augmentation followed by
`baseSectionMap`. It follows that the actual epsilon section reduces to zero.
Consequently `reductionMap_sectionMap` and `reductionMap_sectionEquiv` prove
that actual reduction, in the canonical coordinates of `DualNumberStructure`,
is precisely first-coordinate projection.

## Units and coefficients

`unitReduction f U` is the induced homomorphism on actual units, and
`UnitKernel f U` is its multiplicative kernel. Its elements are actual units on
the inverse-image open whose restriction to `U` is one.

`splitKernelEquiv f U` restricts `Units.mapEquiv (sectionEquiv f U)` to the
split and actual kernels, using the proved first-coordinate formula in both
directions. Composing with the published `DualNumberUnits.kernelEquiv` gives

```
unitKernelEquiv f U : Multiplicative Γ(X, U) ≃* UnitKernel f U.
```

For a section `a`, the underlying actual unit is
`1 + projection.app U a * epsilonSection f U` (`unitKernelEquiv_val`).
Addition of coefficients therefore corresponds to multiplication of these
actual units. `unitKernelAddEquiv` gives the same equivalence in additive
notation. `unitReduction_surjective` proves that every unit on `U` lifts,
by the actual projection section map; the reduction identity proves that this
is a section of reduction. All assertions apply to every open, without an
affineness or finiteness hypothesis.

## Restriction and sheaf condition

`sectionEquiv_naturality` restates the established naturality of `sectionMap`.
Testing on its surjective components proves `reductionMap_naturality` for the
actual maps. `unitKernelMap` restricts actual units to smaller inverse-image
opens. `unitKernelMap_equiv` proves that this restriction is coefficientwise
restriction under `unitKernelEquiv`.

`unitKernelPresheaf` has these actual kernels as values and actual unit
restriction as maps, written additively. The identity and composition laws
follow from the actual structure presheaf. `unitKernelPresheafIso` identifies
it naturally with the additive underlying structure presheaf of `X`.
Transferring the sheaf condition along that isomorphism proves
`unitKernelPresheaf_isSheaf`, and `unitKernelSheaf` packages the resulting
sheaf of abelian groups on `X`.

## Provenance and scope

This is an internal compatibility and transport construction from
`DualNumberThickening`, `DualNumberStructure`, and `DualNumberUnits`. The new
geometric step is the computation of reduction using the actual scheme-map
identities and naturality of `Scheme.ΓSpecIso`; the kernel identification then
uses the already proved coordinate description and split unit equivalence.
No external classification result is assumed. This module establishes the
actual sectionwise reduction kernel and its sheaf condition. It does not yet
classify line-bundle deformations or rigidifications, identify their classes
with derived cohomology, or prove the final tangent-to-H1 comparison.
