# Existence of normalized regular orbital profiles

`regularOrbitalProfileExistence.{u,v}` proves the Library's
`RegularTransferProfileExistenceStatement.{u,v}`. It exposes the profile
construction used in `Langlands.BaseChange.RegularTransfer` for use in
local constancy of concordance and globalization.

On the base group the parameter map lists the characteristic coefficients
of the regular matrix. On the upper group it lists the characteristic
coefficients of the rational norm of the twisted-regular matrix. The
coefficient invariance theorems show that conjugation and twisted conjugation
preserve the respective parameters and regular loci. Equality of the two
parameters is equivalent to norm association by
`normCoefficients_eq_iff_associated`.

The normalization theorem gives associated Haar measures on the ordinary
and twisted centralizers and compatible quotient measures. The ordinary and
twisted orbital charts, together with the compact open neighborhood basis
in the parameter space, give the normalized orbital profiles through
`regularOrbitalProfilesFromCharts`. This yields integrable orbital integrands
and locally constant normalized orbital integrals for Schwartz–Bruhat tests.

This is the profile step of the regular-support argument in
Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle* (2011), I.2.5–I.2.8, printed pp. 17–21.
The source ID is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
(SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`).
