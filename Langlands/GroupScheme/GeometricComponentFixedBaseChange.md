# Base-field extension on Galois-fixed geometric components

This derived unit extends the actual geometric base-field comparison to the
full Galois-fixed component subgroups. It imports
`GeometricComponentRationalBaseChange` and reuses Mathlib's existing continuous
restriction homomorphism of absolute Galois groups.

Let `k` and `K` be arbitrary fields in one universe, with `Algebra k K`, and let
`H` be an actual group scheme over `Spec k`. Assume `Smooth H.X.hom` and
`IsAffineHom H.X.hom`. Fix
`Algebra (AlgebraicClosure k) (AlgebraicClosure K)` and
`IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K)`. Thus the specified
closure embedding is compatible with the canonical map through `K`. There is
no algebraicity, separability, perfection, characteristic, connectedness or
reductivity hypothesis on the field extension or group.

Write `H_K = baseChanged k K H`, write `E_H` for
`geometricComponentBaseChangeEquiv k K H`, and write `rho` for
`Field.absoluteGaloisGroup.mapOfAlgebra k K`. The carrier
`GeometricComponents k H` is the full connected-component group of the actual
pullback to the chosen algebraic closure. The subgroup
`geometricComponentFixedSubgroup k H` consists of elements fixed by every
element of `Field.absoluteGaloisGroup k`.

`geometricComponentBaseChangeEquiv_restrict_smul` proves

```text
E_H (rho(tau) • c) = tau • E_H(c)
```

for every absolute Galois automorphism `tau` of `K` and every geometric
component `c` of `H`. Here `rho` is the actual continuous restriction through
the same specified closure embedding. The proof uses
`AlgEquiv.restrictNormal_commutes` on each closure coefficient to discharge
the compatibility premise of `geometricComponentBaseChangeEquiv_smul`.
Continuity is supplied by the imported Mathlib construction; this unit does
not define a second restriction map.

`geometricComponentFixedBaseChange k K H` is the homomorphism

```text
geometricComponentFixedSubgroup k H
  →* geometricComponentFixedSubgroup K H_K.
```

Its value on `c` has underlying component `E_H(c.val)`, as recorded by
`geometricComponentFixedBaseChange_val`. For each `tau`, the preceding action
identity rewrites its action as the image of `rho(tau) • c.val`; source
fixedness makes this equal to `E_H(c.val)`. The identity and multiplication
laws are inherited from `E_H`. The theorem
`geometricComponentFixedBaseChange_injective` forgets the subgroup
memberships and applies injectivity of `E_H`.

`geometricComponentFixedBaseChange_rational` identifies the restriction of
this map to the existing rational-class injection:

```text
geometricComponentFixedBaseChange k K H
    (rationalGeometricComponentToFixed k H q)
  = rationalGeometricComponentBaseChangeToFixed k K H q.
```

The proof is subgroup extensionality followed by
`geometricComponentBaseChangeEquiv_rational`. This holds for every element
`q` of the ordinary quotient `RationalComponentQuotient H`. Although the new
full-fixed map uses the specified closure embedding, its value on this rational
image agrees with the earlier construction, which needs no such embedding.

For any actual homomorphism `f : H ⟶ H'` between smooth affine group schemes
over `k`, the file supplies three naturality laws.
`geometricComponentBaseChangeSectionHom_naturality` compares the actual
closure-valued section maps before and after applying `f` and its iterated
pullback. It applies the two injective coefficient equivalences to reduce to
`geometricComponentBaseChangeSectionHom_coefficient`,
`baseChangeCoeffEquiv_map` and `affinePointsTarget_naturality`.

The private helper `coefficientBaseChangeEquiv_target` supplies the remaining
coefficient comparison. It holds for any compatible field tower `k → K → M`
and any group-scheme homomorphism over `k`, without smoothness or affineness
assumptions. Applying `Over.OverMorphism.ext` and taking the underlying scheme
map in `baseChangePointsEquiv_comp` proves it using the two projection formulas.

`geometricComponentBaseChangeEquiv_naturality` states

```text
E_H' (geometricComponentMap k f c)
  = geometricComponentMap K (baseChange(f)) (E_H(c)),
```

where `baseChange(f)` is `(GroupScheme.baseChange (baseMap k K)).map f`.
Its proof chooses a closure-valued section in the component using
`geometricComponentOfPoint_surjective` and applies the section law.
`geometricComponentFixedBaseChange_naturality` is the same identity on full
fixed subgroups, proved by subgroup extensionality.

All new laws are intrinsic to the constructed maps and the published actual
section and component comparisons. This is internal derived provenance, with
no new external structure theorem. No surjectivity of restriction or of the
fixed-subgroup map, effective descent, general embedding independence,
identification of fixed components with rationally represented components, or
comparison with points of an fppf quotient is asserted.
