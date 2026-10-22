# Descent from a proved cochain Leibniz identity

This module is an internal construction in namespace
`Langlands.Tate.OrdinaryCup`. It works over a commutative ring `R`, a group
`G`, and representations `A`, `B`, `C`, all in arbitrary common universe `u`.
It uses the actual Mathlib inhomogeneous cochain complexes and their actual
`groupCohomology` objects. No finiteness or flatness assumption is made.

## Input and degree transport

The input `cp` is an `R`-bilinear family from cochains in degrees `p`, `q`
to cochains in degree `p + q`. The second input `leibniz` is a proof, for all
cochains `f`, `g`, of

```text
d (cp p q f g) = transport (cp (p + 1) q (d f) g)
                    + (-1 : R)^p • cp p (q + 1) f (d g).
```

`transport` is the canonical linear equivalence induced by an equality of
natural degrees. The first summand uses `(p + 1) + q = (p + q) + 1`;
the second has degree `p + (q + 1)`, definitionally `(p + q) + 1`.
`transport_apply` expresses transport of a cochain as precomposition with
`Fin.cast`. `transport_trans` proves composition of transports.
`differential_eq_transport` identifies a complex differential along a successor
relation with the standard inhomogeneous differential, and
`differential_transport_source` transports its source degree.

## Construction and its certificates

`cycles_of_leibniz` substitutes zero for both input differentials. Bilinearity
then shows that `cp` preserves cocycles.

`boundary_left_of_leibniz` produces an actual target boundary witness when
the first argument is an incoming boundary and the second is a cocycle.
At degree zero the incoming differential is zero by the complex shape.
At degree `p + 1`, the primitive is transported from the short complex's
predecessor degree to degree `p`. The witness is its `cp` product with the
second cocycle in degree `p + q`. The Leibniz identity and inverse degree
transports show that its differential is the requested product.

`boundary_right_of_leibniz` handles an incoming boundary in the second
argument. At degree zero it again uses the zero incoming differential.
At degree `q + 1`, the target primitive is `(-1 : R)^p` times the `cp`
product of the first cocycle with the transported second primitive. Its
differential is the required product because `((-1 : R)^p)^2 = 1`.
This argument also applies in characteristic two and does not divide by a
scalar.

`fromLeibniz` supplies these three proved certificates to the published
`fromCochains` construction, yielding an `R`-bilinear map

```text
groupCohomology A p →ₗ[R] groupCohomology B q →ₗ[R]
  groupCohomology C (p + q).
```

`fromLeibniz_π_π` proves that on two cocycle classes the result is the class
of their `cp` product, packaged as an actual cocycle by `onCocycles`.

## Provenance and scope

The construction and proofs are self-contained internal deductions from the
explicit input Leibniz identity, bilinearity, the Mathlib complex shape, and
the published `OrdinaryCupDescent` helper. This module does not assert a
literature translation or prove Leibniz for a particular cochain formula.
It is a reusable conditional helper: the final ordinary cup operation must
supply the actual explicit cochain pairing and its independently proved
Leibniz identity. It does not define `ordinaryCup` or establish a comparison
with Tate cohomology.
