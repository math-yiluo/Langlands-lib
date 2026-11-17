# Products of unit opens in connected field group schemes

Worker 876.

This internal helper extends the published smooth-field-group
open-product argument to connected group schemes locally of finite type over
any field. It uses the published irreducibility theorem
`DynamicBaseConnected.irreducibleSpace_of_finiteType`.

For an open immersion into such a group whose image contains the unit,
`surjective` proves that multiplication restricted to two copies of that open
is surjective. Here the product is the actual morphism
`RelativeIdentityComponent.fieldOpenProduct G i`, from the fibre product of
two copies of the open over the base field to `G`.

For a rational point `x`, the proof meets the open and its inverse translate
under `z ↦ z⁻¹ x` in the irreducible ambient group. The unit lies in the first
open and `x` lies in the second. At a point of their intersection, passing to
its residue field gives two actual points in the open whose product is the
restriction of `x`.

To handle an arbitrary scheme point `y`, pull back to the residue field
`κ(y)` and use its canonical rational lift. Connectedness of a field group
is geometric because the unit is a rational section, so the pulled-back
group remains connected and the preceding argument applies.
`range_baseChange` identifies the range of the actual pulled-back product
with the inverse image of the original range. Projecting the rational lift
back to `y` establishes surjectivity. This range comparison does not itself
require connectedness, local finite type, or the open-immersion hypothesis.

Multiplication is flat by the group shear isomorphism and flatness over a
field. Its restriction to open factors is therefore flat. The two flatness
lemmas do not require connectedness or local finite type. `cover` packages
the actual restricted product as a one-member flat cover of the group,
indexed by a one-element type.
The statements impose no smoothness, reducedness, affineness, or separatedness
hypothesis.

This helper supplies a geometric propagation input for local centrality.
It does not assert a centralizer theorem or the fibrewise-centrality target.
