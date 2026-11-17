# Isomorphisms of affine groups over finite coefficients

Worker 875. This is an internal application of published affine-limit
isomorphism descent and general finite coefficient homomorphism descent.

`exists_fg_isIso` treats a specified map of affine finitely presented schemes
over a ring: if it becomes an isomorphism after base change to an arbitrary
algebra, it is an isomorphism after base change to some finitely generated
coefficient subalgebra. It applies the published affine-limit theorem to
the cofiltered system of all finitely generated coefficient subalgebras.

`IsomorphismModel R A G H` records a finitely generated coefficient
subalgebra of `A` and an actual group-scheme isomorphism between the two
groups after base change to it. For affine finitely presented groups,
`exists_isomorphismModel` constructs such a model from an isomorphism
over `A`, retaining any prescribed finite subset of `A`. General
homomorphism descent first descends the forward homomorphism. The
specified-map result makes it an isomorphism after a further finite
coefficient enlargement. The original group laws then lift that scheme
isomorphism to a group-scheme isomorphism.

`isomorphismModel` chooses a model. The record asserts existence of an
isomorphism at the coefficient stage; it does not assert that its
pullback equals a prescribed original isomorphism. No flatness, smoothness
or commutativity premise is imposed. All rings and schemes lie in one
arbitrary universe.

`exists_fg_isDiagonalizable` applies this construction to the diagonalizable
group over the original coefficient ring. Given a diagonalizable presentation
after base change, with any finitely generated full character group including
torsion, it produces a diagonalizable presentation at a finite coefficient
stage retaining the prescribed finite subset. The diagonalizable
base-change isomorphism identifies the constant model at each stage.
