# Global scalar-denominator presentations and local quasi-isogenies

This internal construction connects the actual global tensor
F tensor_O Hom(M,N) with the local rational Hom sheaf and its
quasi-isogeny condition. It builds on `LocalQuasiIsogeny` and its
derived distinguished-scalar formulation of Rapoport–Zink's local
definition. It makes no new literature theorem claim.

`RationalHom.ScalarIsogenyPresentation π z` gives one global exponent n
and an actual integral isogeny f such that π^n z is its rationalization.
This hypothesis is stronger than the condition allowing a different
exponent and integral representative near each point. Coefficient base
change preserves a presentation because it preserves the actual
integral isogeny condition and acts linearly on tensor Hom.

`ofDenominator` constructs the presentation of π^(-n) times an actual
integral isogeny, using the explicit hypothesis that π has nonzero
image in F. `ofIsogeny` uses exponent zero.

The global-to-sheaf map respects field scalar multiplication. The image
of an integral rationalization is the image of its actual structural
coefficient extension to Γ(Spec R). These equations give
`isLocallyScalarIsogeny` for the image of every global presentation:
the top open itself is a witnessing neighbourhood at each point.
`toLocalQuasiIsogeny` retains the nonzero scalar hypothesis and the
actual π-divisibility of both formal modules, hence nilpotence of π
on the base.

`LocalQuasiIsogeny.ofIso` and `refl` give examples from actual integral
isomorphisms and the identity. Their integral kernels and affine fppf
local lifting were constructed in the earlier kernel modules.

O is a commutative ring, and F is an O-algebra field in the same
universe as the coefficient rings. No fraction-field property is
needed for these constructions. The source and target have fixed
global finite coordinates.

No converse is asserted: arbitrary local quasi-isogenies are not
shown here to have a single global denominator. Nor is a presentation
identified with the earlier invertible-tensor `QuasiIsogeny`. General
composition, inverses, height independence, rigidity and
representability remain outside this module.
