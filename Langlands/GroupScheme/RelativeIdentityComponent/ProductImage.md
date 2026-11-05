# Product images and residue-fibre comparisons

This internal helper compares multiplication of a test map after actual base
change with base change of its multiplication map. Naturality of the lax
monoidal comparison and the definition of the base-changed group law give
the map equality. The comparison is an isomorphism, so these maps have the
same topological range. The underlying pullback square then identifies this
range with the inverse image of the original product range. No smoothness,
finiteness or base-change restriction enters this comparison.

For a smooth group over a field, the raw identity-component scheme from
`FieldGeometry` is smooth and geometrically connected. Its square is connected:
the projection has geometrically connected fibres and is open, and the target
is connected. Multiplication of its inclusion maps the pair of unit sections
to the ambient unit, so the connected image lies in the ambient identity
component. Any test map whose image lies in that component factors through
its open inclusion. Factoring both copies proves that its product map also
has image in the component.

For a smooth group over an arbitrary base, apply this field result to every
actual residue fibre. The product range comparison identifies these field
product ranges with the ranges of the base-changed original product map.
The published all-test range criterion then proves that multiplication of a
test map with image in the relative identity set still has image there.

The provenance is internal derivation from the genuine group pullback law,
monoidal naturality, the published scheme pullback image formula, the raw
component's geometry, and continuous images of connected spaces. This file
retains the unconditional openness and existence obligations of the parent
task; it does not assert either conclusion.
