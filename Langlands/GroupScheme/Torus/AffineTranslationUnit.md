# Global units and the affine translation grading

`AffineCoordinates.coordinateUnit` transports a global unit on an affine group
scheme to a unit in its chosen coordinate algebra. The map pulls back along the
affine coordinate isomorphism and applies the global sections isomorphism for
the resulting spectrum. The evaluation formula follows from naturality of the
global sections isomorphism.

Let `i : D(M) ⟶ H` act on an affine group scheme by left translation. Suppose
that pulling back a global unit along a translated point multiplies its
original value by evaluation of the translating point at `m : M` on every
relative test scheme. `CharacterAction.coordinateUnit_mem_component` places
the corresponding coordinate unit in the degree-`m` component.

The proof uses the universal character and the constant algebra map as its
test. The affine comparison for points of `D(M)` gives the monomial of degree
`m` with coefficient one. Multiplying it by the constant image of the unit
gives the single coefficient required by the component membership condition.
This is an internal consequence of the affine point comparison and the
translation coaction over an arbitrary commutative base ring.
