# Compact integration and positivity reflection for sesquilinear forms

This internal prerequisite extends the Library's compact-picture integration
construction from positive forms and bilinear pairings to arbitrary complex
sesquilinear forms. It uses the published compact double-coset sections and
scalar nonvanishing lemma from `CompactPairingDuality`. The claims are derived
from those constructions and elementary properties of the Bochner integral;
no additional assertion from the literature is assumed.

The setup is a topological group `G`, a subgroup `P`, a representation `τ` of
`P` on a complex vector space, a subgroup `K` with a measure, and a supplied
sesquilinear coefficient form `b`. Integrability of every actual scalar
pairing is explicit. `integralSesquilinear` integrates the pairings on `K`.
Conjugate linearity, linearity, Hermitian symmetry and action invariance
follow from the corresponding pointwise identities and the supplied
scalar integral invariance.

The reflection results additionally assume that `G` is nonarchimedean and
weakly locally compact, `τ` is smooth, and
`b(τ(q)v, τ(q)w) = δ(q) b(v,w)` for a supplied nonnegative real function
`δ` on `P`. The nonvanishing and positivity-reflection results also
require `μ.IsOpenPosMeasure`: every nonempty open subset of `K` has
strictly positive `μ` measure. No existence of such a measure or scalar
integral identity is asserted. A coefficient vector determines a smooth
compact double-coset section constant with that value on a compact open
subgroup around the identity and supported in its `P`-saturation.

A nonzero coefficient diagonal gives a nonzero integrated diagonal by the
published scalar nonvanishing lemma. The prescribed value holds on
`K ∩ L`, a nonempty open subset of `K` containing the identity, and its
strictly positive measure is essential to this nonvanishing step.
If a Hermitian coefficient diagonal had negative real part, the
corresponding test-section diagonal would
have nonpositive real part everywhere. Its integral would have nonpositive
real part. Nonnegativity of the integrated form would force the real part
to vanish, and Hermitian symmetry would make the integral zero, a
contradiction. This proves `diagonal_nonneg_of_integral`.

For `positiveCore_of_integral`, all these reflection hypotheses, including
`μ.IsOpenPosMeasure`, are retained. The integrated form is assumed equal to a
supplied invariant positive definite form on the actual smooth induction.
If a coefficient diagonal vanishes, covariance and the support of its
test section make the entire test-section diagonal identically zero.
Definiteness of the supplied form forces that section to vanish.
Its prescribed value then shows that the original coefficient vector
vanishes. Together with reflected nonnegativity, this constructs an
`InnerProductSpace.Core` on the coefficient space. The result does not
assert invariance under a separate Levi action; that must be supplied
when using the core to construct an invariant positive form.
