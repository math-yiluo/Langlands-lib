# Coordinate-smooth parameter families of actual affine group points

Let `R` be a commutative ring, `G` an actual group scheme over `Spec R`,
and `A` a bundled commutative `R`-algebra. Let `B` be a normed commutative
real algebra and fix any ring homomorphism `c : A →+* B`. The coefficient
ring `A` needs no topology, and continuity of `c` is not assumed.
The parameter space `M` is a charted space with a real model with corners `I`.
The universe of the smooth test algebra `B` is independent of the universe of
`R` and `A`; the parameter model and source universes are independent as well.

`CoordinateSmooth` is a proposition about a family `p : M → G.affinePoints A`.
It requires, for every global regular function `a` on `G`, that
`x ↦ c (G.affinePointEvaluation A (p x) a)` be real `C∞` on `M`.
The codomain of each test is the usual normed-space manifold on `B`.
The points and their group operations are the existing actual relative
scheme morphisms; this definition introduces no replacement point carrier.

The following preservation results are proved:

- A constant family is coordinate-smooth.
- Postcomposing with any morphism of the underlying relative schemes preserves
  coordinate-smoothness. This morphism need not preserve the group operation:
  its pullback on global functions gives the required tests.
- Inversion preserves coordinate-smoothness, by applying the preceding result
  to the inversion morphism of the group scheme.
- If the underlying scheme of `G` is affine, pointwise multiplication preserves
  coordinate-smoothness. No finite-type, algebraic smoothness or reductivity
  assumption is used.

For multiplication, the implemented proof first treats the spectrum of a
commutative Hopf algebra. The spectrum point equivalence identifies actual
evaluation with the corresponding algebra homomorphism. Convolution evaluates a
product through comultiplication. Tensor-product induction expresses any fixed
comultiplication value using finitely many sums and products of coefficient
evaluations; real smooth addition and multiplication in `B` preserve the
criterion. The equivalence between affine group schemes and commutative Hopf
algebras then transfers this argument along an actual group-scheme isomorphism.

This is internal derived infrastructure, proved from the existing
scheme-evaluation and Hopf-algebra constructions and Mathlib's smooth maps.
The Hopf proof route adapts the evaluation argument in
`AffinePointTopologicalGroup`; no external analytic-manifold theorem is invoked.
The module does not put a charted-space or manifold structure on
`G.affinePoints A`, assert that a coordinate-smooth family is continuous into a
specified topology, or identify the criterion with an existing manifold
smoothness notion. A general algebraic-smooth-to-analytic manifold construction
and the specific general-linear comparison are separate obligations.
