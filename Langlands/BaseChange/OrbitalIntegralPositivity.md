# Positivity of ordinary orbital integrals

`Langlands.BaseChange.orbitalIntegralPositivity` proves
`Langlands.BaseChange.OrbitalIntegralPositivityStatement.{u}`. Its source is the
positivity used in Henniart–Lemaire, *Changement de base et induction automorphe
pour GL_n en caractéristique non nulle*, Mém. SMF 124 (2011), II.6.8, printed
pp. 124–125. Section I.2.4, printed pp. 14–16, gives the underlying orbital
integral over the left cosets of the centralizer. The Library statement uses
compactly supported Schwartz–Bruhat functions over characteristic-zero
nonarchimedean local fields. In II.6.8 the functions carry a central character.

For the supplied regular semisimple element `γ`, the proof pulls the test
function back along `regularSemisimpleOrbitHomeomorph` and the inclusion of the
closed conjugacy orbit. This identifies the published orbital integrand and
proves its continuity and compact support. Nonnegativity in `ComplexOrder`
implies that the integrand is real-valued and its real part is nonnegative.
The real part at the identity coset is strictly positive, since the integrand
there is the test function evaluated at `γ`.

Compatibility supplies a regular quotient measure and, by
`IsCompatible.isOpenPosMeasure`, positive mass on every nonempty open set.
Regularity gives finiteness on compact sets. Mathlib's
`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero` uses continuity
and compact support to obtain integrability and gives a strictly positive
integral of the real part. The proof rewrites the complex integrand as the
inclusion of its real part, commutes that inclusion with integration using
`integral_complex_ofReal`, and transfers positivity back to `ComplexOrder`.

The registered source identifier is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
The PDF has SHA-256
`7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
Sections I.2.4 and II.6.8 correspond to PDF pp. 22–24 and 132–133, respectively.
