# A unit of order one in the actual maximal unramified field

For a nonarchimedean local field `F : Type u`,
`MaximalUnramified.baseUniformizerUnit F` is the image in
`(inertiaFixedField F)ˣ` of the existing chosen unit
`SplitTorusValuation.uniformizerUnit F`. It is obtained with `Units.map` of
`algebraMap F (inertiaFixedField F)`.

The theorem `orderUnits_baseUniformizerUnit` says that its source-positive
integer order for `MaximalUnramified.valuation F` is one.
`order_baseUniformizerUnit` says the same for the real order
`IntegerValuation.order` used by the KP apartment. The existential form is
`MaximalUnramified.exists_order_eq_one`.

These declarations are internal adapters derived entirely from published
Library constructions. The integer-order proof applies
`MaximalUnramified.orderUnits_base_eq_fieldOrderUnits` to identify the order
on the embedded base unit with its base-field order, then applies
`SplitTorusValuation.fieldOrderUnits_uniformizerUnit`. The real-order proof
casts the resulting integer equality to `ℝ`. All declarations retain
arbitrary universe `u` and use no local-field instance on the inertia fixed
field.

The adapter supplies the order-one unit hypothesis in the integer-valuation
affine-root-system theorem when it is specialized to the maximal unramified
field. It makes no claim about the existence of building data or any affine
root-system axiom.
