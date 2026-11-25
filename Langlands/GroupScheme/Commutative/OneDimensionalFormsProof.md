# Smooth connected affine groups of dimension one

`Langlands.GroupScheme.oneDimensionalGroupForms.{u}` proves
`Langlands.GroupScheme.OneDimensionalGroupFormsStatement.{u}`, the published
statement of Milne, *Algebraic Groups* (2017), Corollary 16.16, printed p. 329.
It gives the finite separable multiplicative form and the finite purely
inseparable additive form in the original universe, together with the
classification over an algebraically closed field.

## Proof

The proof uses Milne's no-torus criterion in its published homomorphism form
(`noTorusUnipotent`, Proposition 17.81). If every closed torus in `G` has trivial
range, the same holds for every homomorphism from a torus. The Library theorem
`torusImageClosedTorusStatement` factors each such map through a closed torus.
Consequently `G` is unipotent.

Unipotence, smooth relative dimension one, affineness and connectedness persist
under passage to the perfect closure inside the algebraic closure. The
published classification `perfectFieldOneDimensionalUnipotent` gives an
isomorphism with the standard one-dimensional vector group there. The vector
group commutes with base change, so `exists_finiteIntermediateField_iso`
descends the isomorphism to a finite intermediate field. This field is purely
inseparable over the ground field because the perfect closure is. For an
algebraically closed ground field the perfect-field classification applies
directly.

Otherwise choose a closed torus whose inclusion is nonzero. The theorem
`torusFiniteGaloisSplitting` supplies a finite Galois splitting field.
Pullback along the field extension is faithful and preserves zero morphisms,
so the base-changed inclusion is nonzero. Base change preserves its being a
closed subgroup. Over an algebraically closed ground field,
`toriAreSplit_of_isSepClosed` splits the original torus.

In either split situation the torus has positive Lie dimension. A split
torus indexed by the empty type is a zero object, so every homomorphism
from it is zero. The ambient Lie dimension is one. A proper smooth closed
subgroup of the smooth connected ambient group would have strictly smaller
Lie dimension by `Lie.dimension_lt_of_proper_closedSubgroup`. The inclusion
is therefore an isomorphism. The split torus has one factor because its Lie
dimension equals the cardinality of its index type. The categorical product
on that singleton is the multiplicative group.

The source statement and its geometric interpretation are documented in
[OneDimensionalFormsStatement.md](OneDimensionalFormsStatement.md). The
finite splitting input is Milne 12.19, and the perfect-field unipotent
classification is the converse in Milne 14.58 with Corollary 14.53.
