# Continuity of the intrinsic modular character

This internal analytic unit proves continuity of Mathlib's actual modular
character for any locally compact topological group. The group has arbitrary
universe `u`, with its supplied group law and topology. No Hausdorff,
second countability, nonarchimedean, unimodularity, or supplied continuity
hypothesis is required.

`Langlands.Haar.continuous_modularCharacter_of_locallyCompact` states continuity of
`MeasureTheory.Measure.modularCharacter : G →* ℝ≥0`.
`continuousModularCharacter` packages that same homomorphism as a
continuous monoid homomorphism. Its application theorem is definitionally
the original modular character.

The proof chooses a real nonnegative compactly supported continuous
function nonzero at the identity. Its integral against the fixed left
Haar measure is positive. The theorem
`coe_modularCharacter_eq_integral_div` identifies each real-valued modular
value with

\[
\Delta(g)=
\frac{\int_G f(xg)\,d\mu(x)}{\int_G f(x)\,d\mu(x)}.
\]

It uses Mathlib's Haar scalar-factor comparison and its compact-test
integral ratio, then changes variables along the measurable right
translation. This is the positive right-pushforward convention for the
intrinsic modular character. The denominator is a proved nonzero constant.
No right invariance or inner regularity premise is introduced.

The auxiliary theorem `continuous_integral_mul_right` works for any
Borel measure finite on compact sets. For a compact neighborhood `U` of
the translation parameter, every translated test is supported in
`tsupport f * U⁻¹`. This is a compact set. Joint continuity of group
multiplication and the compact-support parametric integral theorem give
continuity on `U` and hence at the original parameter. Dividing this
continuous integral by the fixed denominator proves real-valued
continuity; the nonnegative-real embedding gives the desired continuity.
The proof locally chooses only the Borel measurable structure used to
define the intrinsic modular character.

The provenance is derived internally from the pinned Mathlib definitions,
Haar uniqueness and compact-support integration theorems. It uses the
same local uniform compact-support argument as the existing subgroup
averaging continuity proof, without a subgroup or quotient construction.
This general continuity result supports extending adelic modular
comparisons from dense finite-place truncations to all actual adelic
points. It does not establish the local determinant/Jacobian comparison,
reductive determinant triviality, or the universal adelic Haar
unimodularity statement.
