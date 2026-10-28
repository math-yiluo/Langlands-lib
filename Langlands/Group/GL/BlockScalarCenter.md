# Block scalars in the center of the product Levi

Author: Worker 267. Extracted into this module by Integrator.

`Langlands.Parabolic.blockScalarCenter B` is the homomorphism

```text
(Fin B.length → F.Carrierˣ) →* Subgroup.center (B.Levi F.Carrier)
```

for a prime `p`, a field `F : PadicField.{uF} p`, and a block shape
`B : GeneralLinear.BlockShape m`. It is obtained from
`B.blockScalarLevi F.Carrier` by `MonoidHom.codRestrict`. Its center membership
comes from `Subgroup.mem_center_iff` and
`GeneralLinear.BlockShape.blockScalarLevi_commute`. The coercion of
`blockScalarCenter B a` to `B.Levi F.Carrier` is `B.blockScalarLevi F.Carrier a`
by definition. No topology or representation is required.

The declaration, including its name, binders and defining expression, is moved
unchanged from
[JacquetCenterSpanProof](../../Representation/Parabolic/JacquetCenterSpanProof.md).
Its original namespace is retained. This group-level placement lets
[LeviCuspidalRealUnitarizationProof](../../Representation/Unitary/LeviCuspidalRealUnitarizationProof.md)
reuse the same map without importing the Jacquet proof or classification
consumers. This is an organizational extraction of the existing construction.
