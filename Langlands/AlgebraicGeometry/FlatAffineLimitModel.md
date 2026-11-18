# Flat affine models along affine limits

Worker 875.

`Langlands.AlgebraicGeometry.FlatAffineLimit.model` chooses a flat affine
locally finitely presented model of a supplied affine scheme over one level of
a small cofiltered diagram of affine schemes. The diagram is given with an
actual limiting cone and an isomorphism of its point with `Spec A`. The input
morphism `f : X -> Spec A` is flat and locally of finite presentation, and `X`
is affine. No noetherian or flatness condition on the diagram maps is imposed.

The resulting `Model` contains a level, an affine source scheme, a flat locally
finitely presented map to that level, a map from the original `X` to the model,
and an actual pullback square recovering `f`. The bottom map of this square
is the cone projection transported through the specified limit isomorphism.
Surjectivity, a specified source point, and uniqueness of the model are not
asserted.

The construction uses finite coefficients over a same-universe copy of the
integers. `exists_coefficientModel` first applies the published affine scheme
finite-coefficient model theorem, then the published flatness descent theorem
to pass to a larger finite coefficient subalgebra. The two finitely generated
coefficient extensions are noetherian and have finite type over that copy of
the integers, hence finite presentation. A pullback gives the flat model and
its recovery square. The resulting noetherian coefficient spectrum is locally
of finite presentation over the terminal integer spectrum.

`nonempty_model` factors the map from the limit to that coefficient spectrum
through one diagram level, using Mathlib's finite-presentation factorization
theorem. All maps to the integer spectrum agree by terminality. Pulling the
coefficient model back to this level gives the requested affine flat model;
cancellation of the right pullback square proves the exact recovery square.
`model` chooses the resulting data.

This is an internal consequence of the published affine scheme
finite-coefficient and flatness descent theorems, noetherian finite-type
algebra facts, and affine-transition limit factorization. The implementation
uses explicit scalar actions for the lifted integer ring. It is a generic
model construction and does not prove relative multiplicative-type descent
or the host extension theorem.
