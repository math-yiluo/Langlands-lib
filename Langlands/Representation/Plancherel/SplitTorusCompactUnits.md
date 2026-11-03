# Compact units and smooth split-torus characters

This internal prerequisite for Renard V.3.19 uses the actual canonical rational
point topology. A complex character with open kernel has norm one on a compact
subgroup: its kernel restricts to an open subgroup of finite index, so every
character value on the compact subgroup has a positive integral power equal to
one. Taking complex norms proves the assertion.

The field's valuation-one sphere is closed in the compact valuation unit ball.
The embedding of field units into the field then proves compactness of the
actual integral-unit subgroup `FML.unitGroup`. This generalizes the argument in
the published `LocalField.SmoothCharacterNormProof` from its `PadicField`
interface to arbitrary-universe nonarchimedean local fields of both
characteristics.

For the actual finite coordinate split torus, the published affine coordinate
homeomorphism, composed with `rationalPointsAffineHomeomorph`, identifies the
canonical rational-point topology with the product topology on field units.
Its agreement with the original split coordinates is checked by evaluating the
actual projection characters. The common norm kernel is exactly the product of
the integral-unit subgroups, by the published `SplitTorusValuation` kernel
comparison, and hence is compact. The empty coordinate type is allowed.

The compactness and finite-index arguments are derived supporting results, not
additional assumptions about the smooth character.
