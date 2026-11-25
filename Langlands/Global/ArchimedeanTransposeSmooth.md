# Transpose inverse on actual archimedean smooth functions

This is internal infrastructure for
`CuspidalTransposeInverseContragredientStatement`. It constructs the
pullback by transpose inverse on the Library's actual smooth-function space and
identifies the induced actions with the algebra involutions in
`ArchimedeanTransposeInverse`. The construction is derived from the definitions
of the units manifold, the genuine matrix directional derivative, scalar
extension, and the universal enveloping algebra. No representation-theoretic
contragredient identification is used.

The hypotheses are an arbitrary-universe number field `F` and a natural number
`n`. Smoothness is real smoothness in the mixed real and complex archimedean
coordinates of the existing Library. `matrixTransposeLinear` is continuous
real-linear matrix transpose. The group map `theta(g) = (g⁻¹)ᵗ` is smooth:
inversion is smooth on the units manifold, transpose is continuous linear, and
the open embedding of the units into matrices detects smoothness. The two
coordinate identities show that this map agrees with transpose inverse in the
original infinite adele coordinates.

`smoothTranspose F n` is the complex-linear equivalence sending `f` to
`f ∘ theta`. Transpose inverse is an involution, so the inverse pullback is the
same map. The group automorphism identity gives covariance of right translation:

```text
smoothTranspose (R(theta(h)) f) = R(h) (smoothTranspose f).
```

The derivative proof works with the ambient matrix map
`matrixInverseTranspose(a) = (Ring.inverse a)ᵗ`, which agrees with the group map
at units. Mathlib's derivative of ring inversion at a unit gives

```text
d theta_g(H) = (-g⁻¹ H g⁻¹)ᵗ,
d theta_g(g X) = theta(g) (-Xᵗ).
```

`smoothDifferential_eq_of_extension` allows this ambient extension to compute
the Library's actual directional derivative, since it agrees on the open set of
units. The ordinary Frechet chain rule then proves
`smoothTranspose_smoothDifferential`. This identifies the differential twist
with `realLieIota`; it is not an assumed covariance law.

Tensor-product induction extends the covariance to `complexLieIota`. Quotient
induction on the universal enveloping algebra and algebra induction on the
tensor algebra extend it to every enveloping element. Restricting the result to
the genuine center gives the analogous center-action identity. In every case
the orientation is

```text
smoothTranspose (action(iota(a)) f) = action(a) (smoothTranspose f).
```

The range description of the center-orbit span and surjectivity of `centerIota`
show that the center orbit of `smoothTranspose f` is the linear image of the
center orbit of `f`. Restriction of the pullback gives a linear equivalence
between those two spans, so `isCenterFinite_smoothTranspose_iff` proves both
preservation and reflection of center finiteness.

This module concerns archimedean smooth functions and their actual differential
operators. It does not construct an adelic automorphic realization or
identify such a realization with a contragredient. Those are separate steps
towards `CuspidalTransposeInverseContragredientStatement`, which is proved as
`cuspidalTransposeInverseContragredient` in
`Langlands.Global.RankinSelberg.CuspidalTransposeInverseContragredientProof`.
