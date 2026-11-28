# The twisting isometry of the full cuspidal space

`GroupSchemeCuspidalTwistEquivStatement` uses the rational quotient and the
compatible algebraic and adelic automorphisms of
`GroupSchemeTwistCuspidalInvarianceStatement`. It gives a surjective complex
linear isometry of the full almost-everywhere cuspidal `L²` space. On ambient
`L²` classes it agrees with `twistOperator`, pullback by the inverse quotient
automorphism. It satisfies \(U R(a) = R(\Theta a) U\) for the cuspidal right
action.

The inverse adelic automorphism is induced by the inverse group scheme
automorphism by functoriality. On the quotient, the two induced maps are
inverse by evaluating them on representatives. Measure preservation then
holds in both directions by `MeasurePreserving.symm`. Applying
`groupSchemeTwistCuspidalInvariance` to each direction gives a pair of maps
on the same cuspidal space. The pullback composition rule on `Lp` shows
that these maps are inverse. `norm_twistOperator_apply` gives the isometry,
and `IsotypicTrace.twistOperator_quotientL2RightTranslate` gives covariance
after passing to the cuspidal subtype.

This is a consequence of the Library's cuspidal invariance and translation
covariance lemmas. The spectral use of the twist is in Henniart–Lemaire,
*Changement de base et induction automorphe pour GLₙ en caractéristique non
nulle* (2011), II.6.4, printed p. 120 (PDF p. 128). There the twist carries
each cuspidal representation into the summand of its twisted class.

Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
