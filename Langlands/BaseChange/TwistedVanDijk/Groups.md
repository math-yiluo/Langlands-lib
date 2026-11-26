# Integral points, the Iwasawa factorization and the entrywise automorphism

Module `Langlands.BaseChange.TwistedVanDijk.Groups`. For a nonarchimedean local field `E`, a
block shape `B` of `n` with standard parabolic `P = B.parabolic E`, Levi `M = B.Levi E` and
unipotent radical `U = B.unipotentSubgroup E`, and an automorphism `σ` of `E` over a topological
field `F` (with `E` carrying the `F`-module topology), it collects the group-theoretic facts used
by the proof of the twisted van Dijk formula (`Langlands.BaseChange.TwistedVanDijk.Proof`).

## Integral points

- `integralGL E r` abbreviates `GL_r(𝒪_E)`, the Library's
  `GeneralLinearGroup.integralSubgroup` for the valuation ring of `E`.
- `exists_parabolic_mul_integralGL`: the Iwasawa factorization `G = P K`, `K = GL_n(𝒪_E)`. It
  is deduced from the Library's `Iwasawa.exists_mul_upperTriangular` (every element is an upper
  triangular element times an integral one), since upper triangular elements lie in every
  standard block parabolic (`BlockShape.mem_parabolic_of_isUpperTriangular`).
- `leviProjection_mem_integralGL`: the Levi blocks of an integral parabolic element are
  integral (they are diagonal blocks of the matrix and of its inverse).
- `leviEmbedding_mem_integralGL_iff`: a block diagonal element is integral exactly when its
  blocks are (the off-diagonal entries are zero).
- `leviEmbedding_mul_mem_integralGL_iff`: `m u` (`m ∈ M`, `u ∈ U`) is integral exactly when `m`
  and `u` are. The Levi projection of `m u` is `m`; integrality of `m u` gives that of `m` by
  the previous item and then that of `u = m⁻¹ (m u)`.

## Coordinates on the parabolic

These hold over any commutative ring `R`.

- `BlockShape.unipotentSubgroup_le_parabolic`, and `leviEmbedding_conj_mem_unipotentSubgroup`:
  conjugation by a block diagonal element preserves `U` (normality of the unipotent radical in
  the parabolic).
- `parabolicProduct (m, u) = m u`, with inverse `p ↦ (m_p, m_p⁻¹ p)` (`parabolicUnipotentPart`),
  forms the bijection `parabolicProductEquiv : M × U ≃ P`; `leviProjection_parabolicProduct`
  computes the Levi part.
- `parabolicProduct_mul`: left multiplication in coordinates,
  `m₀ u₀ · m u = (m₀ m) (m⁻¹ u₀ m · u)`.
- For a topological ring, `parabolicProductHomeomorph : M × U ≃ₜ P` (both directions are
  continuous: the Levi embedding and projection are continuous).

## Topology and `σ`

- `isCompact_integralGL`, `isOpen_integralGL`: `GL_r(𝒪_E)` is compact and open, from the
  compactness and openness of `𝒪_E`.
- `algEquiv_mem_integer_iff`: an `F`-automorphism of `E` preserves and reflects integrality. It
  is continuous (`continuous_algEquiv`), and the Library's
  `LocalFieldData.mem_integers_iff_of_continuous_ringEquiv` applies.
- `entrywiseAut_mem_integralGL_iff`: hence the entrywise action `entrywiseAut σ r` preserves
  `GL_r(𝒪_E)`, in both directions.
- `entrywiseAut_mem_unipotentSubgroup_iff`: the entrywise action preserves `U`; it preserves
  the parabolic (`entrywiseAut_mem_parabolic_iff`) and the diagonal blocks are the identity
  exactly when their images are, `σ` being injective and fixing `0` and `1`.
- `entrywiseContinuousAut σ r` is `entrywiseAut σ r` as an automorphism of topological groups.
