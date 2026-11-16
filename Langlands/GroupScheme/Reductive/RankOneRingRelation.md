# The rank-one relation with arbitrary second coordinate

This internally derived construction extends `RankOneRingSquareRoots` to remove
the unit hypothesis on the second coordinate of the rank-one relation. Its
provenance is the imported unit-coordinate relation, elementary ring and group
identities, and the affine spectrum/global-sections correspondence. It asserts
no new identification with an external source.

For any commutative ring `R`, `UnitSumExtension.Ring R` is the total quotient ring
of `R[T]`, namely its localization at the nonzero divisors. It is a commutative
ring even when `R` has zero divisors; no field or domain instance is used.
`UnitSumExtension.inclusion` is the injective composition of the constant
polynomial map and the localization map.

For any `x,w : R`, `exists_units` constructs three units in that extension:
`a` is the image of `T`, `b` is the image of `w-T`, and `v` is the image of
`1+xT`. These polynomials are nonzero divisors: their coefficients at degree
one, degree one, and degree zero are respectively `1`, `-1`, and `1`.
Mathlib's coefficient criterion then shows they become units in the total
quotient ring. Thus `f(w)=a+b` and `v=1+f(x)a` for the injective inclusion `f`.
This also covers the zero ring.

`exists_unitSum_test` realizes this construction on any affine test scheme `Z`
over any base scheme. The morphism from `Spec B` to `Z` is the spectrum map of
the inclusion followed by the affine isomorphism to `Z`. The imported
`appTop_specMap_isoSpec_inv` identifies its pullback on global sections with the
inclusion followed by the inverse of `ΓSpecIso`. Consequently the pullback is
injective, and it carries `w` to a sum of units `a+b` with `1+f(x)a` a unit.

The remaining results take supplied `WeylData D` over an arbitrary commutative
ring `k`, exactly as in `RankOneRingCalculus`, and assume that the ambient group
scheme is affine. In particular, the actual normalizer, its torus-valued square,
the reflection equation and the cell decomposition with unit coordinates remain
hypotheses. No existence of this data is proved here.

On any test scheme let `β` denote the pullback of `D.cβ`, let `A` and `B` be
the supplied positive and negative root maps on scalar points, and let `H`
be the supplied cocharacter. `relation_of_unitSum` supposes
`w=a+b`, `v=1+Xa`, and `u=1+Xw`, where `a,b,v,u` are units. Set `q=u/v`.
Then `q=1+(X/v)b`. Applying `relation_of_unit` first to `(X,a,v)` and then to
`(X/v,b,q)` gives the desired product. The negative root weight for `H(v)`
scales the second negative coordinate by `v⁻²`. The resulting coordinates
combine because

```
u*a+b = v*w,
v*q = u,
q⁻¹*v⁻¹*X = u⁻¹*X.
```

All scalar calculations use unit inverses and commutative-ring identities.

For an affine test `Z`, `relation_affine` applies this calculation after the
injective refinement from `exists_unitSum_test`. Naturality of the scalar root
points, cocharacter and base coefficients gives the pullback of the claimed
identity. The imported `points_ext_of_injective_appTop` descends this equality
into the affine ambient group. Finally `relation` applies the affine result
on the canonical affine cover of an arbitrary test scheme and uses equality of
scheme morphisms on that cover.

The resulting equation is, for arbitrary global sections `X,w` and any unit
`u=1+Xw`,

```
A(X) B(β*w) = B(β*u⁻¹*w) H(u) A(u⁻¹*X).
```

There are no square-root or unit hypotheses on `X` or `w`, and no reducedness,
noetherian, Henselian or characteristic hypothesis. The unit `1+Xw`, the affine
ambient group and the supplied actual Weyl data remain necessary inputs to this
result. Equality is never detected only on field-valued points. The unconditional
local Isomorphism Theorem remains outside this contribution.
