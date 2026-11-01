# Reduction to the base model-star identity

`AdjacentRankBaseModelStarIdentity` names the model-star equality at ambient
`w * zeta`, for every original algebraic test tensor. The right side uses the
full plus Fourier transform of its Schwartz factor, the original coefficient at
`w * inverseTranspose(h^-1)`, and the original character action. This internal
condition is not a new premise in the final model-star statement.

The published `Padic.adjacentRankModelIntegral_mul` action law moves a
right ambient factor into the input tensor. Its only
remaining scalar is the outer character and normalized determinant weight.
Apply the base condition to `rho0(inverseTranspose k) Psi`, with `k=zeta*g`.
The published Fourier covariance, in the companion covariance helper, replaces
its Fourier transform by `|det k|^(r+1) rho0(k)(H Psi)`. Pulling the scalar
through evaluation and the total Bochner integral is unconditional. The action
prefactor is `chi^-1(det k)|det k|^(-(r+1)/2)`, so combining the powers gives
exactly `chi^-1(det k)|det k|^((r+1)/2)`.

The result proves only this implication from the base equality to the arbitrary
ambient equality. It does not yet prove the base equality or claim completion.
The proof is an internal derivation from the model definitions and the established
fixed-character Fourier covariance. It retains independent field/module
universes, zero rank, zero functional, reducible representations and every
algebraic tensor; it needs no smoothness or irreducibility for this implication.

The determinant calculation reuses the published
`RankOneGammaTwist.determinant_inverseTranspose`.
