# Full integral-image comparison of the normalized CM presheaf

This is an internal consequence of `HarrisTaylorCMIntegralExistence` and the
existing unpointed integral-image and disconnected normalized CM presheaf
constructions. It introduces no new source assertion.

The inputs are the actual universe-zero Harris CM data, `Prerequisites` `P`,
the full generic `ProperFibreAmpleAffineOpenStatement`, the named torsion,
duality-naturality, Weil and adelic premises. The generic geometric statement
remains an explicit parameter of all existence results and isomorphisms.
The existing admissible and componentwise admissible categories retain all
their original objects and actual over-category morphisms.

For a connected admissible base, `integralCMFamilyCondition_all` applies
`integralCMClassCondition_all` separately to every actual geometric point of
an existing compatible unpointed family. It does not choose a preferred
point or change any member of the family.
`integralCMUnpointedClassEquiv` gives the original subtype inclusion as a
bijection; its inverse pairs the unchanged family with the proved integral
condition. These equivalences assemble into
`integralCMUnpointedClassTowerIso` and then
`integralCMUnpointedClassPresheafIso`.
The latter's forward transformation is definitionally the existing
`integralCMUnpointedClassImagePresheafInclusion`, as the theorem with suffix
`_hom` records. Thus the comparison uses the previously constructed
point-independent family and actual base pullback.

For a componentwise admissible base `X`,
`IntegralCMDisconnectedFamilyCondition` requires that the value of the
original disconnected family on every actual connected component scheme
satisfy `IntegralCMFamilyCondition`. This is a condition on the existing
Harris product, including its original empty-product value on an empty base.
`integralCMDisconnectedFamilyCondition_all` proves it component by component.

The componentwise condition is preserved by every original level
transporter, by `integralCMFamilyCondition_map`. It is preserved by every
actual base morphism by applying `integralCMFamilyCondition_pullback` to
`componentCMBaseHomTo`, from each source component to its actual image
component. These stability proofs do not require the fibre-ampleness premise.

`IntegralCMDisconnectedClassImageTower` is the exact subtype of the
existing disconnected class tower defined by this condition.
`integralCMDisconnectedClassImagePullback` restricts the original
disconnected pullback. Its functorial laws follow after forgetting the
subtype proof from the corresponding laws of
`disconnectedClassTowerPresheaf`.
They define `integralCMDisconnectedClassImagePresheaf` on the full
`ComponentwiseAdmissibleCMBaseCategory`, retaining every original level arrow.

Finally, `integralCMDisconnectedClassEquiv` pairs each unchanged product
family with the universal integral-condition proof. Its forward map is the
subtype value. The resulting
`integralCMDisconnectedClassTowerIso` is natural in every original level
arrow, and `integralCMDisconnectedClassPresheafIso` is also natural in
every original base morphism. Naturality is definitional because all image
maps restrict the existing maps, and the forward comparison forgets only
the condition proof. The theorem with suffix `_apply` records this exact
forward function.

The integral image here is a subpresheaf of the original normalized class
presheaf; it retains the original rational-isogeny relation and adelic
invariant level orbits through its imported constructions. This unit proves
that the subpresheaf is the full presheaf under the displayed premises.
It neither identifies it with an ordinary polarized finite-level
representable moduli functor nor constructs a representing scheme.
Smoothness, projectivity under division, admissibility of a representing
scheme, and discharge of the generic fibre-ampleness premise remain
obligations for `DivisionCMRepresentabilityStatement`.
