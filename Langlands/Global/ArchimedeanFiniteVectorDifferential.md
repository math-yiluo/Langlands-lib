# Actual differentiation of finite-coordinate vector valued smooth functions

This internal construction reuses the existing genuine scalar smooth
function differential and complexified Lie action on the actual
completion-based archimedean matrix group. The number field and finite
coefficient index have independent universes; rank zero and an empty
coefficient index are allowed. Coefficients are all vectors in `iota -> C`
with their supremum norm, not a chosen invariant subspace.

`finiteVectorSmoothEquiv` identifies the existing vector valued smooth
function space with all finite families of existing scalar smooth functions.
The two functions are the same coordinate evaluations in the original group
coordinates. Smoothness of a finite-coordinate map is equivalent to smoothness
of each coordinate, giving both directions. This complex-linear equivalence
also intertwines right translation coordinate by coordinate.

The scalar endomorphism action extends to all coordinate families pointwise.
Its algebra-homomorphism laws and conjugation by the genuine coordinate
linear equivalence transport the proved scalar Lie action to
`finiteVectorSmoothLieAction`. Thus its bracket law is proved intrinsically
by existing scalar calculus, with no supplied Lie-action premise.
`finiteVectorSmoothDifferential X` restricts this action to the actual real
Lie direction using the existing complexification map.

`finiteVectorCoordinateExtension` is the vector of the existing scalar
units-chart expressions. It agrees with the original vector function on all
invertible matrices. The scalar expressions are smooth near every invertible
matrix, hence the finite vector expression is genuinely differentiable there.
The coordinate Frechet derivative theorem proves that the transported real
differential is exactly the actual vector valued Frechet derivative in the
left-invariant matrix direction `g * X`. The convention remains the one for
right translation `R(h)f(g) = f(g*h)`.

No topology on the smooth function space is assigned. No algebraic coefficient
representation, analytic-versus-dual-number differential equality, compact
insertion, automorphic cohomology or occurrence assertion is assumed or proved
by this unit. It supplies the vector differentiation infrastructure for such
later comparisons using the existing actual function space.
