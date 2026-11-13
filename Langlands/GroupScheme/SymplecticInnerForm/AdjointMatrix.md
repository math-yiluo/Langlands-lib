# Matrix algebra action of a supplied symplectic adjoint quotient

Let `K` be any field, `n` a finite index type, and `q : M ⟶ A` a
supplied adjoint quotient of actual group schemes over `Spec K`. Given an
isomorphism `i : M ≅ SymplecticMatrix.groupScheme n K`, this module
extends the quotient's inner action to the full matrix algebra on `n ⊕ n`.
There is no restriction on the field characteristic or on the size of `n`.

`pointMatrix` identifies `M`-points on every relative test scheme with
symplectic matrices over its global sections. `affineMatrix` gives the
corresponding coordinates over a commutative `K`-algebra `L` itself.
Both comparisons commute with pullback of coefficients. The lemmas
`pointMatrix_affine` and `pointMatrix_comp_affine` compare the two
coordinate conventions through the canonical global-sections map.

For an affine-test point `c` of `A`, the construction pulls `q` back
along `c`. Its universal point lifts `c` to `M`. This pullback is a flat
surjective cover, so its map on global sections is injective.
The generic pullback, coefficient-map and injectivity constructions are
reused from the published `SpecialLinearInnerForm/AdjointMatrix` module;
they do not depend on a special-linear presentation.

`pointMatrix_inner_lift` identifies the given inner action over this cover
with conjugation by the universal lift's symplectic matrix.
`conjugation_image_symplectic` consequently places the conjugate of
every symplectic matrix over `L` in the image of coefficient pullback.
The full symplectic matrix-span lemma then supplies the preimages needed
by the injective algebra-map descender.

`adjointMatrixHom hq i c` is the resulting `L`-algebra endomorphism of
the matrix algebra. `adjointMatrixHom_map` identifies it with conjugation
after pullback to the universal cover.
`adjointMatrixHom_symplectic` says that on symplectic points it is the
original inner action. `adjointMatrixHom_map_lift` proves the same
conjugation formula after any further pullback. Using the published
matrix-extension construction and injectivity on global sections,
`pointMatrix_innerAction` identifies the original action on every
relative test over `Spec L` with scalar extension of this algebra map.

`adjointMatrixHom_one` gives the identity algebra map at the identity
point. `adjointMatrixHom_mul` identifies multiplication of adjoint points
with composition of their algebra maps. `adjointMatrixHom_naturality`
proves compatibility with every homomorphism of commutative
`K`-algebras. These follow by the full-span extensionality lemma and
the corresponding laws of the supplied inner action.

This is a derived internal construction. Its proof adapts the published
special-linear matrix-action argument to the symplectic point model and
the new symplectic span theorem, while reusing the presentation-independent
pullback and matrix-extension machinery. It assumes an adjoint quotient
and a split symplectic presentation; it constructs neither an inner-form
descent algebra nor a descended involution, and proves no classification.
