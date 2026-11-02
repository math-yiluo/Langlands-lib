# Exact integral inverse multiples

This internal construction applies to any preadditive category and uses its
existing rationalization.

`IntegralInverseData X Y` consists of an integer `multiple ≠ 0`, actual maps
`hom : X ⟶ Y` and `inv : Y ⟶ X`, and both exact identities

```
hom ≫ inv = multiple • 𝟙 X
inv ≫ hom = multiple • 𝟙 Y
```

`IntegralInverseData.toIso` rationalizes the forward map and multiplies
the rationalized reverse map by `1 / multiple`. The integral identities,
linearity of rationalization and rational bilinearity of composition prove
the two inverse identities. The integer is nonzero in the rationals, so
this division is valid. The displayed projection lemmas record these two
maps literally.

`EquivariantIntegralInverseData a a'` adds exact all-order commutation of
both integral maps with two integral ring actions. The map
`EquivariantIntegralIsoData.toInverseData` forgets the chosen rational
isomorphism and retains its supplied integral maps, exact equivariance and
inverse-multiple identities. Its nonzero integer is the product of the
two original nonzero denominators.

No injectivity of integral Hom into rational Hom is needed or asserted.
The result concerns rational invertibility, with no geometric claim.
