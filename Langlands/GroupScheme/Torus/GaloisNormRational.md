# Rational-point compatibility of the algebraic Galois norm

Worker 1435. Derived comparison infrastructure for the actual morphism
`GaloisNorm.norm`, the existing `GaloisPointComparison.rationalNorm` and the
existing rational-point carriers. No new point group or norm is introduced.

The reused `GaloisPointComparison.rationalCoeffEquiv_map` proves naturality of the existing rational/coefficient
comparison for an arbitrary group-scheme morphism by equality of the underlying
scheme maps. This avoids expanding the norm construction in the rational proof.

The fields `k,L` occupy an arbitrary common universe, with finite-dimensional
Galois extension structure. The target is a commutative affine group scheme
`T` over `Spec k`; write `T_L` for its actual ordinary group-scheme base change.

`tensorUnitMap` is the coefficient map `L tensor_k k → L` from the standard
tensor-unit algebra isomorphism, restricted to `k` scalars.
`tensorUnitMap_extend` identifies its composite with tensor extension as the
existing field-coefficient extension. `tensorUnitMap_conjugate` identifies the
two actual conjugation actions. `tensorNorm_eq` applies the injectivity of
field-coefficient extension, the conjugate-product formulas for both norms,
and the two preceding comparisons.

`baseChange_rationalCoeff` compares the affine pullback equivalence with
`GaloisPointComparison.baseChangeCoeffEquiv`, by their identical underlying
scheme morphisms: the rational section followed by the first pullback
projection.

With the affine and locally finite type instances on `T_L` required by
`AffineWeil.groupScheme`, `rationalPointsEquiv` is exactly the composite

```
rationalCoeffEquiv L T_L
  then (AffineWeil.basePointsEquiv k L T_L).symm
  then (rationalCoeffEquiv k (AffineWeil.groupScheme k L T_L)).symm.
```

`rationalPointsEquiv_coeff` cancels the final inverse equivalence to give the
prescribed affine coefficient point.

`norm_rationalPoints` states that applying `rationalPoints.map` of the actual
algebraic norm to this point gives the existing
`GaloisPointComparison.rationalNorm`. Its proof moves to the injective
base-field coefficient comparison, uses the all-algebra norm formula,
`tensorNorm_eq`, naturality of the actual pullback equivalence and the
tensor-unit definition of `AffineWeil.basePointsEquiv`.

The ordinary and commutative actual base changes used in this equality are
definitionally the same underlying group scheme. The statement uses the
ordinary `GaloisPointComparison.baseChanged` domain directly.
No characteristic, splitness, topology or smoothness hypothesis enters.
