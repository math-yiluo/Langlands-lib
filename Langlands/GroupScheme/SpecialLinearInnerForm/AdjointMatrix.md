# Matrix action of an adjoint quotient

This derived support construction extends the inner action of an actual adjoint
quotient of a special linear group to its matrix algebra. It uses the published
`IsAdjointQuotient.innerAction` and a supplied isomorphism of its source with
`SpecialLinear.groupScheme n K`. The base is an arbitrary field; coefficient
algebras are arbitrary commutative algebras over it. The finite index type may
be empty or a singleton. No characteristic restriction is imposed.

`pointMatrix` and `affineMatrix` transport the published special-linear point
coordinates through the given isomorphism. Their comparison applies the inverse
global-sections/spectrum isomorphism. `sectionMap` pulls coefficient elements
back along a morphism to the affine coefficient test scheme. The point
coordinates are natural under all test morphisms; affine coordinates are also
natural under all coefficient algebra maps. `sectionMap_comp` describes
composition of tests. `sectionMap_ringTestMap_comp` states that composing a
test with `Spec f` composes its coefficient homomorphism on the right with `f`.

The pullback of an adjoint point along the quotient gives `liftTest`, with its
projection `liftBase` and lift `liftPoint`. The projection is an epimorphism
because the quotient is flat and surjective. Consequently its pullback on global
functions is injective; for an affine coefficient test this also makes
`sectionMap` injective. `liftTestMap` and its two projection identities make the
universal lifts compatible with arbitrary changes of test scheme.

On the universal local lift, the supplied inner action is conjugation. Acting on
a determinant-one matrix defined over the coefficient ring therefore gives a
matrix still defined over that ring. The spanning result from `MatrixSpan`
extends this image containment to all matrices. `adjointMatrixHom` then descends
the conjugation algebra endomorphism by the injective coefficient map.
`adjointMatrixHom_map` gives the resulting conjugation equation on the
universal lift. `adjointMatrixHom_specialLinear` identifies its value on an
affine special-linear point with the given inner action.

`adjointMatrixHom_map_lift` pulls the conjugation equation back along
`liftTestMap`. The central compatibility theorem `pointMatrix_innerAction`
then handles every test `s : V ⟶ Spec L` and point `g : V ⟶ M.X`: the matrix
of the inner action at `s ≫ c` is `extendMatrix (sectionMap s)` applied to the
matrix of `g`, using the linear map underlying `adjointMatrixHom hq i c`.
To prove this, the universal lift over `V` makes both sides conjugation by
the same matrix. The extension is identified with conjugation by its values
on matrix units, and injectivity of the lift's pullback on global functions
reflects the equality back to `V`.

`adjointMatrixHom_one` and `adjointMatrixHom_mul` prove the identity and
composition laws. `adjointMatrixHom_naturality` proves compatibility with
every coefficient algebra map, hence with Galois automorphisms. These laws
follow by checking on special-linear matrices using the supplied action's
laws and naturality, then applying `linearMap_ext_specialLinear`. For
coefficient naturality, the target is viewed as a module over the original
coefficient ring through the coefficient map.

These declarations are derived support for the task's twisting construction; no
inner-form classification theorem is asserted by this module. The provenance
is internal and derived: the proof uses elementary matrix algebra, the
published adjoint action, and flat-surjective pullback of schemes.
