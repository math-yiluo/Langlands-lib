# Restriction and coefficient extension of the discriminant factor set

Let \(f\colon M\to M'\) be a field embedding equivariant for a homomorphism
\(\rho\colon \operatorname{Gal}(M'/F')\to\operatorname{Gal}(M/F)\).
`transferredLift` and `transferredFactor` precompose the arguments with
\(\rho\) and apply \(f\) to the matrix entries and factor values.
For a subgroup \(H\) of \(\operatorname{Gal}(M/F)\), the transferred
action uses the subgroup \(\rho^{-1}H\).

`transferredLift_mul` transports the projective multiplication identity.
`twistedAct_transferredLift` transports the semilinear matrix action. The
proofs use that entrywise extension commutes with transpose and inverse.
The determinant, the sign, and the distinction between the two cosets also
commute with this transfer. Applying these facts to the determinant formula
of `Langlands.Algebra.UnitaryDiscriminant.Cocycle` proves
`detCocycle_transferredLift`. These calculations allow independent field
universes for the two Galois groups.
