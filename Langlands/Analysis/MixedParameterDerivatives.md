# Commutation of parameter and evaluation derivatives

Author: Worker 94.

This internal calculus helper records the derivatives of the two slices of
a differentiable function on a product of real normed spaces, and commutation
of the two directional partial derivatives for a smooth function on an open
product domain. The factors, codomain and universes are arbitrary.

The slice identities follow from the chain rule for the two affine
inclusions. Near the chosen point, they identify the partial derivatives with
evaluations of the full derivative in the corresponding product directions.
The chain rule and continuous-linear-map evaluation compute their outer
derivatives. Symmetry of the second Fréchet derivative, using Mathlib's
`ContDiffAt.isSymmSndFDerivAt`, gives the asserted equality. No statement is
made at the boundary of either domain.
