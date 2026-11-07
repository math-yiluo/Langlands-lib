# Monic equivariant additive maps and entire root subgroups

This internal derived unit starts with an actual additive-group homomorphism
over an arbitrary field and its scalar torus-equivariance law on every relative
test scheme. It converts that law into equivariance of the actual weight action,
proves stability of the map's image on every test, and shows that the whole
differential image lies in the stated character space.

For a monic map and a supplied one-dimensional target weight space, the
differential image equals that weight space. Monicity gives injectivity of the
actual differential; standard vector coordinates identify the source Lie algebra
with a one-dimensional vector space, so equality follows by finite dimension.
The construction `rootLieEquiv` is the resulting linear equivalence with the
entire root weight line; its value in the ambient Lie algebra is exactly the
original differential.

If the ambient group is connected reductive, the torus is a split maximal
torus, the character is an actual root, and no higher positive integer multiples
are roots, the map represents the entire intrinsic root subgroup on every
relative test scheme. The proof uses closedness of monic homomorphisms from
smooth connected affine groups and the proved uniqueness of root subgroups
from their full positive Lie span. The final theorem derives the target's
one-dimensionality from the split-root Lie-line theorem.

All hypotheses remain explicit. The unit constructs no torus, root datum,
parametrization, or highest-weight module; it identifies a supplied monic
equivariant map with the full root functor. It is derived from the imported
Library results and uses no external literature.
