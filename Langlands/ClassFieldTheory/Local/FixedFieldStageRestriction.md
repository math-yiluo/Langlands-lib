# Fixed-field subgroup-stage comparison and restriction

This construction identifies the actual target of finite-stage restriction on
algebraic-closure units with relative fixed-field cohomology. It works for every
characteristic-zero field `K : Type u`, with arbitrary common universe `u`, and
every natural degree `q`. All declarations are in
`Langlands.ClassFieldTheory.Local`.

## Canonical finite-stage comparison

Let `E` be a finite Galois intermediate field of `AlgebraicClosure K`, let
`H = finiteGaloisFixingSubgroup K E`, and let `N` be an open normal subgroup of
the absolute Galois group with `h : N.toSubgroup ≤ H.toSubgroup`. Put
`F = finiteStageFixedField K N` and `A = absoluteUnitDiscreteModule K`, using
these unchanged exports from `FixedFieldStages`.

`finiteStageFixedField_contains` proves the actual inclusion `E ≤ F` from
subgroup containment. This inclusion lemma itself does not need characteristic
zero, finite dimensionality, or the Galois hypothesis on `E`.
`finiteStageRestrictedAlgebra K E N h` is the algebra structure induced by
`IntermediateField.inclusion` for that inclusion. The certificates
`finiteStageRestrictedTowerBase K E N h` and
`finiteStageRestrictedTowerTop K E N h` prove the scalar towers `K → E → F`
and `E → F → AlgebraicClosure K`, respectively. Both proofs compare the actual
algebra maps, whose underlying values agree definitionally. These structures
and certificates are explicit arguments installed with `letI` where needed;
there is no independently chosen algebra structure in the finite-stage exports.

With this canonical algebra structure, `finiteStageRestrictedRelativeIso K E N h q`
has source exactly

```lean
groupCohomology
  (finiteQuotientRep (A.restrict H.toSubgroup).toRep
    (restrictOpenNormal H.toOpenSubgroup N)) q
```

and target `relativeCohomology E F q`. This is precisely the target of the
published `finiteRestriction A H.toOpenSubgroup N q`, without replacing that
restriction or its coefficient module.

`finiteStageRelativeIso_restriction K E N h q` proves the equality

```lean
finiteRestriction A H.toOpenSubgroup N q ≫
    (finiteStageRestrictedRelativeIso K E N h q).hom =
  (finiteStageRelativeIso K N q).hom ≫ relativeRestriction K E F q
```

with the canonical algebra and base scalar tower installed in its type. The
proof also explicitly installs the upper scalar-tower certificate. Both maps
on the right are the unchanged published maps.

## Intrinsic algebraic construction

The implementation first works with any same-universe Galois extension `L/K`,
an intermediate field `E`, and a closed normal subgroup `N` of `Gal(L/K)`.
Write `F = IntermediateField.fixedField N.toSubgroup`. The generic comparison
uses an `Algebra E F` compatible with the canonical inclusions through the two
scalar towers `K → E → F` and `E → F → L`. It assumes no group or coefficient
equivalence and no comparison identity.

`le_fixedField_of_le_fixingSubgroup` applies the order-reversing Galois
connection to `N ≤ E.fixingSubgroup`. The generic canonical structure
`fixedFieldRestrictedAlgebra` and certificates `fixedFieldRestrictedTowerBase`
and `fixedFieldRestrictedTowerTop` supply the structures used by the finite
specialization.

`fixedFieldRestrictedGroupHom` sends an automorphism fixing `E` to its
restriction on `F`, now viewed as an automorphism over `E`. It composes
`IntermediateField.fixingSubgroupEquiv E` with normal restriction. The field
`F` is normal over `E` because it is normal over `K`. Surjectivity follows from
extension of automorphisms along a normal extension. The kernel is
`N.toSubgroup.comap E.fixingSubgroup.subtype`: restriction is the identity
exactly when the ambient automorphism fixes `F`, and the infinite Galois
correspondence identifies `F.fixingSubgroup` with the closed subgroup `N`.

`fixedFieldRestrictedGroupEquiv` is the resulting quotient equivalence

```text
E.fixingSubgroup / (N ∩ E.fixingSubgroup) ≃ Gal(F/E).
```

The denominator here is implemented as the subgroup comap, not as a new
abstract group. `fixedFieldRestrictedGroupEquiv_commutes` proves that this
identification commutes with inclusion in the ambient quotient: composing
`quotientSubgroupMap` with `InfiniteGalois.normalAutEquivQuotient N` equals
composing the relative equivalence with `AlgEquiv.restrictScalarsHom K`.
Quotient induction reduces this to equality of restrictions of the same
ambient automorphism.

For `h : N ≤ E.fixingSubgroup`, `fixedFieldRestrictedUnitsEquiv` composes the
inverse of `fixedRestrictionEquiv` with `fixedFieldUnitsLinearEquiv`. It sends
an invariant unit for the restricted representation to the unit of `F` with
the same ambient value. The first equivalence uses `h` to recover invariance
under every element of `N`; the second identifies invariant units with units
of the actual fixed field. The scalar ring remains `IntegerScalars.{u}`.
`fixedFieldRestrictedUnitsEquiv_intertwines` proves equivariance for the actual
quotient action and the group equivalence. Quotient induction, linear-map
extensionality, unit extensionality and subtype extensionality reduce the
identity to `AlgEquiv.restrictNormal_commutes`.

`fixedFieldRestrictedCohomologyIso` applies `groupCohomology.mapIso` to these
proved equivalences and the equivariance certificate.
`fixedFieldRestrictedCohomologyIso_restriction` expands the comparison
isomorphisms and uses `groupCohomology.map_comp` and `map_congr`. The required
group-map identity follows from `fixedFieldRestrictedGroupEquiv_commutes` by
injectivity of the ambient quotient equivalence. The coefficient-map identity
is definitional: restricting an invariant unit and then identifying its
fixed-field value gives its original fixed-field value. Specializing to
`L = AlgebraicClosure K` and `finiteStageClosedSubgroup K N` gives the stated
finite-stage isomorphism and square.

## Provenance and scope

These declarations are internal construction and map-compatibility
certificates built from `FixedFieldStages`, `FixedFieldUnits`,
`Continuous.QuotientSubgroupCohomology`, and Mathlib's Galois correspondence
and group-cohomology functoriality. Their mathematical context is Serre,
*Local Fields* (1979), Chapter X, §§3–4, printed pages 154–156 (PDF pages
160–162), registered as `serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Section 3 describes infinite Galois cohomology through finite quotient stages;
section 4 describes functoriality of relative cohomology with multiplicative
coefficients. The exact Lean interfaces and the explicit subgroup comparison
are derived implementation details, not separately quoted statements from
Serre. This module proves no finite or absolute H2 exactness claim.
