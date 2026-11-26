# Changing the ambient character in a twisted induced trace

`characterTwistDistribution_induced` compares the character twist of the
twisted distribution of a smooth induction with the twisted distribution
obtained by twisting the inducing representation. It applies to an ambient
smooth character `ψ` invariant under `θ` whose restriction to the parabolic
factors through the inducing-group character `η`, invariant under `θM`.

The equivalence from `Induction.smoothInductionTwistEquiv` multiplies the
induced functions by `g ↦ ψ(g)`. The factorization of `ψ` identifies the new
covariance with that of the twisted inducing representation. Applying the
two twisting operators to the corresponding functions gives the same result
because `ψ(θ⁻¹g) = ψ(g)`. The finite-rank trace is invariant under the
resulting equivalence. Pullback by multiplication of test functions by `ψ`
computes the character twist of the ambient distribution.

This is a derived compatibility of the Library's smooth induction and
character twist with the induced operator formula of Henniart–Lemaire II.4.4.
