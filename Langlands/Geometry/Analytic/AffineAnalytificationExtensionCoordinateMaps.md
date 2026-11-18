# Naturality of extension-valued affine analytic coordinates

`extensionAlgHom_saturatedHom` identifies the coordinates of the image of a
full `L`-valued point under the saturated affine analytification map induced
by `f : A →ₐ[K] B`. They are its coordinates in the source composed with `f`.
The value field `L` is any normed extension of the complete ultrametric
nontrivially normed field `K`.

Choose a containing original source chart and the target chart selected by
the affine map. The corresponding whole charts of the saturated atlases
form an admissible pair. The local-domain pullback restriction equation
identifies the composite through the saturated target and source charts
with the composite through the original target and source charts. The
original pullback is the selected affine bounded pullback, which sends the
image of each coordinate `a` to the image of `f a`. Evaluating this equation
in the saturated source chart identifies the two algebra maps, using the
any-chart formula for recovered coordinates.

`extensionAlgHom_localizedHom` uses the same identity for the localized
map, where the localized field-point functor agrees with the original
field-point functor on these saturated presentations and maps.

`extensionAlgHom_mapValue` applies the any-chart formula before and after
postcomposing the chart characters with an isometric map of value fields.
The resulting algebraic coordinates are postcomposed with that same map.

## Provenance

This is an internal deduction from the affine coordinate recovery formulas,
the two-variable local-domain pullback equation, the published compatibility
of affine chart pullbacks with algebraic coordinates, and the definition of
the localized field-point functor and of `FieldPoint.mapValue`.
