# Arithmetic pullback and archimedean differential actions

Author: Worker 2.

This internal construction concerns the existing smooth complex-valued
functions on the actual completion-based infinite adelic matrix group. The
number fields have independent universes, the matrix rank is every natural
number, and the coefficient values remain unchanged.

The real directional derivative intertwines pullback along an actual field
isomorphism with the real matrix Lie equivalence constructed in
`ArchimedeanLieTransport`. The proof uses the target coordinate extension
composed with the actual continuous real linear matrix map as an extension
of the pulled-back function. It agrees with that function on matrix units.
The existing independence-of-extension theorem permits this replacement.
The real chain rule and multiplicativity of the matrix map carry the
direction `g * X` to the corresponding target direction. Only local
differentiability near units is used.

Tensor induction extends this equation to the complexified Lie action,
fixing complex coefficients. Induction through the tensor algebra and
its enveloping quotient extends it to every actual enveloping operator;
the scalar, generator, product and sum cases use the established algebra
action laws. Restricting through the actual center inclusion gives
center-action covariance.

`centerOrbitSpan_smoothComap` identifies the whole source center-orbit span
of the pulled-back function with the linear image of its target center-orbit
span. The published range description of the orbit span reduces both
inclusions to center-action covariance and surjectivity of the actual center
equivalence. Restricting the smooth-function equivalence gives
`centerOrbitEquiv`. This linear equivalence preserves and reflects finite
dimensionality, proving `isCenterFinite_smoothComap_iff`. No assumption that
all smooth functions are center-finite is made.

`centerFiniteEquiv n e` is the genuine complex-linear equivalence from
`centerFiniteFunctions L n` to `centerFiniteFunctions K n`. It is the
restriction of arithmetic smooth pullback, and its inverse is pullback
along `e.symm`. Its underlying smooth-function and evaluation formulas are
definitional. Identity, contravariant composition, and inverse laws follow
from those of smooth pullback; for `e : K ≃+* L` and `a : L ≃+* M` its
composition law is
`centerFiniteEquiv n (e.trans a) =
 (centerFiniteEquiv n a).trans (centerFiniteEquiv n e)`.

Provenance is internal composition of `ArchimedeanLieTransport`,
`ArchimedeanSmoothDifferential`, `ArchimedeanEnvelopingAction`, and
`ArchimedeanCenterFinite` with
Mathlib's real chain rule and the tensor and enveloping constructions.
No new original-literature identification or automorphic existence
assertion is claimed. The maps are algebraic linear equivalences on the
existing function subspaces; no topology of derivatives, growth condition,
cuspidality, or occurrence assertion is added.
