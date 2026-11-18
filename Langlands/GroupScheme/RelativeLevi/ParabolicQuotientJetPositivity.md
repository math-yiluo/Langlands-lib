# Parabolic determinant-dual ampleness from the actual quotient jet kernels

Fix an actual homogeneous quotient `Q` of a relative parabolic
over `Spec R` with retained jet embedding data `D`.
`HasStabilizedJetKernelComparison` asks for the equality of two
submodules over each affine open of `Q`. The first is the kernel of
the actual tensor generator of the chosen representative's jet
stabilized by the pulled-back complement. The second is the submodule
classified by the retained Grassmannian embedding on the same open,
using the section algebra from `Q → Spec R`.

For proper `Q` and positive jet order,
`homogeneousQuotientLieDeterminantDual_isAmple_of_jetKernels`
turns this equality into ampleness of the actual chosen determinant
dual. The ambient global generator gives the existing surjective
actual jet tensor map. The complement gives an isomorphism on the
other summand, so the stabilized generator is surjective. The
affine-open comparison identifies the Grassmannian quotient with
the stabilized jet sections and retains the specified generators.
The retained closed embedding and the finite projectivity of the
complement give the hypotheses of the positive-order jet ampleness
transfer.

`finiteAffineParabolicDeterminantDualAmple_of_jetKernels` chooses the
published actual data of order at least one on each homogeneous
quotient and uses the published finite-component assembly. It gives
the exact finite-family target from the stated kernel comparisons,
including the empty family.

This internal assembly uses the existing actual jet, Grassmannian
and determinant positivity results. Its remaining premise is the
actual classified kernel equality on the parabolic quotient.
