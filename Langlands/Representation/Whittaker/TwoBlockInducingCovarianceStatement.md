# Scalar covariance of the actual inducing functionals

`Langlands.Whittaker.TwoBlockInducingWhittakerCovarianceStatement` is an internal
prerequisite for the JPSS two-block extension construction. It states that for
any actual vector `f` of the canonical normalized upper induction of the ordered
pair `(π₁, π₂)`, evaluation at `diag(u₁,u₂) g`, followed by the tensor functional
`ℓ₁ ⊗ ℓ₂`, is the value at `g` multiplied by the two standard unipotent
characters. The ranks are `a+1` and `b+1`, including rank one. The coefficient
modules share one universe; the parent extension statement handles independent
universes by lifting its two modules.

Both `ℓᵢ` are elements of the actual `glFunctionals` submodules. There is no
assumed scalar covariance law and no replacement model for induction. Neither
nonvanishing nor irreducibility nor smoothness of the factor representations is
needed for this identity: the vector `f` already belongs to smooth induction.
The normalized modulus contributes one because the two unipotent blocks have
determinant one.

This is a derived statement, extracted from the published definitions of
`twoBlockEval`, `pairFunctional`, `glFunctionals`, and normalized parabolic
induction. Its expected derivation uses
`normalizedProductInduced_covariant`, the Levi section and two-block modulus
formulas, and tensor linearity. It is not a new assertion quoted from the
literature and does not assert integrability or the parent extension theorem.
