# The integral-weight Tits obstruction of an inner simply connected group

Let `G` be an affine locally finite type simply connected group over `k` with
actual Galois pinning data. Suppose the entire Galois action fixes each simple
vertex. Simple connectedness gives generation by the integral coroots. The
published vertex criterion then puts every element of the actual character
lattice into the subgroup fixed by the star action.

`GaloisPinningData.innerTitsObstruction` is the composite of that inclusion
with the published obstruction on the star-fixed subgroup. It is an additive
homomorphism to the actual matrix-stable Brauer quotient. A highest-weight
representation computes its value by the class of its actual Tits algebra.
Any dominant difference computes the same value. Taking the tensor product of
two actual CSA representatives represents addition of the corresponding
weights. `innerAbsoluteTitsObstruction` uses the canonical pinning over the
separable closure and the full absolute Galois action.

This specialization of Tits (1971), Theorem 3.3 and Corollary 3.5, uses the
Library's highest-weight construction and its obstruction on star-fixed
weights. It applies in arbitrary characteristic, including over imperfect
fields, and uses the actual integral weights throughout.
