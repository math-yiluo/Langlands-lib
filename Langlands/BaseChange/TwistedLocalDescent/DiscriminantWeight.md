# The weight `|D_{G/M,σ}|^{-1/2}` from the opposite nilradical

Module `Langlands.BaseChange.TwistedLocalDescent.DiscriminantWeight`. Let `E/F` be nonarchimedean
local fields, `E` a finite `F`-algebra with the module topology, and `|·|_F`, `|·|_E` the
residue-normalized absolute values (`LocalField.residueNormalizedAbsoluteValue`).

- `residueNormalizedAbsoluteValue_norm`: `|N_{E/F}(y)|_F = |y|_E`. Both sides describe how
  multiplication by `y` scales additive Haar measure on `E`: over `E` by
  `WeylHaarScaling.map_mul_residueAbsolute`, over `F` by `map_linearEquiv_residueAbsolute`
  applied to the `F`-linear map `x ↦ y x`, whose determinant is `N_{E/F}(y)`.
- `det_restrictScalars_lowerAdjoint`: `det_F(Ad(m) | 𝔲̄) = N_{E/F}(det_E(Ad(m) | 𝔲̄))`
  (`LinearMap.det_restrictScalars`).
- `residueNormalizedAbsoluteValue_det_lowerAdjoint`: `|det_F(Ad(m) | 𝔲̄)|_F = δ_P(m)⁻¹`, where
  `δ_P` is the Library's `leviModulus`: by `det_lowerAdjoint` and the previous identities the left
  side is `∏_{k < i} |det m_i|_E^{n_k} |det m_k|_E^{-n_i}`, the inverse of the product defining
  `leviModulus`.
- `residueNormalizedAbsoluteValue_det_twistedOperator_sq`: for a cyclic algebra `E/F` of group
  `⟨σ⟩` (`IsCyclicAlgebra σ l`),

  `|det_F(σ − Ad(m)⁻¹ | 𝔲̄)|_F² = |D_{G/M,σ}(m)|_F · δ_P(m)`,

  from `abv_twistedRelativeParabolicDiscriminant` and the previous item.

In Henniart–Lemaire (Mém. SMF 124, 2011), II.4.5, the twisted constant term at `m` carries the
factor `δ_P(m)^{1/2}` and the local descent produces the weight `|D_{G/M,σ}(m)|^{-1/2}`; this
module supplies the identity relating them to the Jacobian `|det_F(σ − Ad(m)⁻¹ | 𝔲̄)|_F` of the
twisted conjugation chart.
