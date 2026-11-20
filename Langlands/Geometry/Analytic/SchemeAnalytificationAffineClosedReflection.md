# Closed immersion reflection for scheme monomorphisms into an affine spectrum

Take a complete, ultrametric, nontrivially normed field `K` and a finite type
`K`-algebra `A` with a supplied finite polynomial presentation. The top
chart of `Spec A` has its actual coordinate ring. The relative spectrum
point of the top chart induces a `K`-algebra isomorphism from `A` to that
ring. The induced map on affine analytic models and the top chart
homeomorphism give `specSchemeComparisonHomeomorph` between the glued
scheme space and the supplied polynomial-locus space.

Let `q : W ⟶ Spec A` be over `Spec K`, with `W` separated and locally of
finite type over `K`. Suppose that a point-family analytification of the
represented space of `W` is supplied, together with a map into the
polynomial-locus affine model compatible with every polynomial
presentation and relative spectrum point. On each source chart,
composition of its ring point with `q` gives the composite of the top
coordinate isomorphism with the affine restriction map. The equality of
these ring maps and the supplied compatibility identify the underlying
map with the glued scheme analytification of `q` under the two comparison
homeomorphisms.

If `q` is quasi-compact and a monomorphism and the supplied analytic map is
an analytic closed immersion, its underlying map is proper. It follows
that the glued scheme analytification is topologically proper. The
algebraic monomorphism is locally quasi-finite, so finiteness follows
from the affine-target properness reflection for quasi-finite morphisms.
Mathlib's finite monomorphism criterion gives a closed immersion.

This construction connects the Library's two analytification models for
the affine scheme tests in the algebraic-space immersion comparison. The
last step follows the proper monomorphism argument in Berkovich,
*Spectral theory and analytic geometry over non-Archimedean fields* (1990),
Proposition 3.4.7(2), printed p. 66 (PDF p. 80), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`.
