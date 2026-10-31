# Inverse-transpose unipotent Fourier identity

This internally derived helper continues the actual unipotent Fourier identity
in `RankOneMatrixFunctionalEquationComparisonUnipotentFourier`. It keeps the
supplied scalar Haar measure, character, and self-duality hypothesis.

`unipotentHaar_isInvInvariant` proves that inversion preserves the actual
integral-normalized unipotent Haar measure. Its proof uses the published right
invariance theorem. The image under inversion is a regular left-invariant
measure, and the integral compact open subgroup has mass one in both measures.
Regular Haar uniqueness therefore gives equality. This is the same elementary
normalization argument used privately for general linear Haar in
`HaarSymmetriesProof`.

`inverseUnipotentFourierPhase` defines the common scalar phase
`ψ(-s(u))` used on both sides of the integral identities.
`unipotentFourierSum_inv` negates the adjacent-entry sum using the actual
unipotent inverse-entry theorem. The negative phase equals the actual inverse
standard Whittaker character, as stated by
`unipotentFourierSum_inverseCharacter`.

For every size `n+1`, `unipotentHaar_iota_fourier_duality` substitutes `u⁻¹`
on the Fourier side of the earlier transpose identity. The substitution
preserves the full product of the group Haar and supplied scalar Haar. Thus
the Fourier side evaluates at `(u⁻¹)ᵗ C(a)`, the original side at `u M(v)`,
and both phases are `ψ(-s(u))`. The theorem includes absolute integrability of
both full product integrands. It applies to any actual group Haar measure
that is invariant under inversion; the instance above supplies this condition
for the integral-normalized measure over a nonarchimedean local field.

The imported `TopologicalData.determinantNorm_inverseTranspose` from
`Representation/Induction/InverseTranspose` follows from transpose invariance
of the determinant and the inverse laws of the determinant and absolute-value
homomorphisms. The final theorem
`padicUnipotentHaar_iota_fourier_duality_right` applies the preceding identity to
the actual Schwartz test `Y ↦ Φ(Y h^iota)`, where `h` has determinant norm one.
The published change of variables for the supplied matrix Fourier measure
identifies its Fourier transform with `X ↦ ΦHat(X h)`. This yields the same
identity with right factor `h` on the Fourier side and `h^iota` on the original
side. Both product integrability assertions are retained, with no additional
normalization constant. No determinant-one restriction stronger than determinant
norm one is needed, and every size including one is covered.

This is a Fourier identity on unweighted affine slices. The weighted extraction
of a common matrix test and coefficient for a given Whittaker vector, and the
gamma comparison itself, remain separate obligations.
