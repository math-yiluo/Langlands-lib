# The Jacquet function of a lifted Levi function

Module `Langlands.Representation.Shahidi.OpenCellJacquet`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `jacquetIntegrandAt ψ hϖ Φ g Y = conj ψ(Y_(t,0)) F(w u'(Y) g)` (via the Library's
  `jacquetIntegrand`) and `jacquetFunction ψ hϖ Φ g = ∫ jacquetIntegrandAt … dY` for
  `matrixHaar`, where `F` is the lift of `Φ`.
- `jacquetFunction_mul_integral`: for a Levi-invariant `Φ`, right invariance under
  `GL((r+1)+(t+1), 𝒪)`.
- `jacquetFunction_intertwiningUnipotent_mul` (no hypothesis on `Φ`): covariance under the
  unipotent radical `U'` by the intertwining character; `jacquetFunction_levi_mul`: for a
  Levi-invariant `Φ` that is Levi-equivariant for characters `θ₁`, `θ₂`, covariance under the
  exchanged block unipotents by `θ₁(u₁) θ₂(u₂)`; `jacquetFunction_unipotent_mul`: when `θ₁`, `θ₂`
  are the standard characters, left covariance under the full upper unipotent group by the
  standard character, using the Library's factorization of upper unipotents
  (`Whittaker.upperUnipotent_exchanged_factorization`). The `integrable_…` versions transfer
  integrability of the integrand along these translations under the same hypotheses.

## Provenance

The Jacquet integral of Shahidi (1984, `shahidi-1984-fourier`, printed page 72, (0.2)) in the
coordinates `w`, `U'`; the covariance computations follow the Library's
`Whittaker.TwoBlockJacquetCovarianceProof`.
