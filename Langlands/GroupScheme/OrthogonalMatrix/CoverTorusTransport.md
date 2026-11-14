# Transport of a supplied orthogonal-cover torus

This internal derived module compares the actual supplied split maximal torus
of a central cover with the standard split orthogonal torus over the original
field. It imposes no restriction on the field or its characteristic.

`characterLattice.exists_comp_eq_iff_kills_kernel` is fpqc character descent:
a character factors through a quasi-compact, flat, surjective group homomorphism
if and only if it sends every point of its full scheme kernel, over every
relative test scheme, to the identity. The forward implication evaluates the
factorization. The reverse implication evaluates at the actual kernel inclusion
and applies `FpqcHomDescent.hom` and its factorization theorem. This argument
retains nonreduced kernels.

`OrthogonalMatrix.exists_standardTorus_square` first constructs the closed
split-torus fppf image of the supplied torus under the central isogeny. The
central-isogeny maximal-torus theorem makes this image maximal. Rational
conjugacy of maximal split tori in the connected orthogonal identity component
then identifies this torus with the standard diagonal torus. Composing the fppf
projection with the resulting torus isomorphism gives the stated square and
flat, surjective, quasi-compact map, all over the original field. The returned
conjugating point lies in the actual identity component.

The provenance is the published fpqc homomorphism descent, split-torus fppf
image, central-isogeny maximality, and rational maximal split-torus conjugacy
results. This module does not prove any numbered-root normalization or vector
weight existence assertion.

`StandardTorusTransport` packages the rational point, torus map, square and three
fpqc properties. `standardTorusTransport` chooses such data from the existence
theorem. The coordinate index is nontrivial, as needed for the published
orthogonal reductivity theorem; finite ranks at least four satisfy this.
