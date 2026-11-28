# The unipotent fibre of a block Levi for σ-conjugation on `GL_n(E)`

The module `Langlands.BaseChange.LeviTwistedFibre` supplies the abstract criterion
`TwistedFibreData.twistedOrbitalIntegral_eq_zero` (module
`Langlands.TraceFormula.TwistedOrbitalFibreVanishing`) with its data on `GL_n(E)`: the unipotent
radical of a standard parabolic subgroup with at most two blocks, at an element of the block
diagonal subgroup whose σ-centralizer lies in that subgroup.

## Setting

`F` is a field, `E` a commutative `F`-algebra with a topology making it a Hausdorff topological
ring, `σ : E ≃ₐ[F] E`, and `θ = (entrywiseAut σ n).toMonoidHom`, the action of `σ` on every entry
(module `Langlands.BaseChange.Norm`). `B` is a block shape of `n` with `B.length ≤ 2`, `M(E)` its
block diagonal subgroup `B.leviSubgroup E`, `P(E) = B.parabolic E` and
`U(E) = B.unipotentSubgroup E` (module `Langlands.Group.GL.Blocks`). The element `δ` lies in
`M(E)` and `twistedCentralizer θ δ ≤ M(E)`.

## Contents

- `leviTwistedFibreData B σ δ hB hδ hH : TwistedFibreData θ δ`, with `U = U(E)`, `P = P(E)` and
  `π = leviEmbedding ∘ leviProjection : P(E) →* GL_n(E)`, the projection onto the diagonal blocks.
  The fields: `U(E)` and `P(E)` are closed (`isClosed_unipotentSubgroup`, `isClosed_parabolic`);
  `U(E)` is commutative and `θ`-stable (`unipotentSubgroup_mul_comm`,
  `map_mem_unipotentSubgroup`, module `Langlands.Group.GL.UnipotentEntries`); `π` is continuous
  (`leviEmbeddingContinuous`, `leviProjectionContinuous`); `π p = 1` exactly when the diagonal
  blocks of `p` are identity matrices, that is when `p ∈ U(E)` (`leviEmbedding_injective`); an
  element `leviEmbedding m` of `M(E)` is `leviInParabolic m`, and `π` returns it
  (`leviProjection_section`); `δ` and the σ-centralizer lie in `P(E)` because `M(E)` does
  (`leviSubgroup_le_parabolic`, module `Langlands.Group.GL.ParabolicQuotient`).
- `leviTwistedFibreData_twist_surjective`: if `E` is a finite `F`-module, the twisted conjugation
  `twist : a ↦ δ⁻¹ a δ θ(a)⁻¹` of this fibre data maps `U(E)` onto itself.

## Proof of surjectivity

Let `V = B.upperBlocks E F`, the `F`-subspace of matrices with vanishing blocks on and below the
diagonal, and `s` the entrywise action of `σ` on matrices. By
`mem_unipotentSubgroup_iff_sub_one_mem`, `g ∈ U(E)` exactly when `g - 1 ∈ V`, and by
`upperBlocks_mul_eq_zero`, `Y Z = 0` for `Y, Z ∈ V`. Hence for `Y ∈ V` the matrix `1 + Y` is
invertible with inverse `1 - Y` and lies in `U(E)`.

- `δ⁻¹ Y δ ∈ V` for `Y ∈ V`, because `δ⁻¹ (1 + Y) δ ∈ U(E)` (`P(E)` normalizes `U(E)`) and
  `δ⁻¹ (1 + Y) δ - 1 = δ⁻¹ Y δ`; and `s(Y) ∈ V`, because `θ(1 + Y) = 1 + s(Y) ∈ U(E)`.
- `L(Y) = δ⁻¹ Y δ - s(Y)` is therefore an `F`-linear map `V → V`; `F`-linearity of `s` is the
  `F`-linearity of `σ`.
- `twist(1 + Y) = (1 + δ⁻¹ Y δ)(1 - s(Y)) = 1 + L(Y)`, since `δ⁻¹ Y δ · s(Y) = 0`.
- `L` is injective: `L(Y) = 0` gives `twist(1 + Y) = 1`, so `1 + Y = 1` by `twist_injective`
  (which uses `H ∩ U = 1`, here a consequence of `H ≤ M(E)`).
- `V` is a subspace of `Matrix (Fin n) (Fin n) E`, a finite-dimensional `F`-vector space because
  `E` is a finite `F`-module, so the injective endomorphism `L` is surjective (Mathlib's
  `LinearMap.injective_iff_surjective`).
- For `v ∈ U(E)`, choose `Y ∈ V` with `L(Y) = v - 1`; then `twist(1 + Y) = v`.

## Provenance

Formulated for this Library. In the two-block case `(k, n - k)` with `δ = diag(d₀, d₁)` and
`a = [[1, X], [0, 1]]`, the twisted conjugation is `X ↦ d₀⁻¹ X d₁ - X^σ`, the map whose
bijectivity underlies the descent of σ-orbital integrals to a Levi subgroup in Henniart–Lemaire,
*Changement de base et induction automorphe pour `GL_n` en caractéristique non nulle*, Mém. SMF
124 (2011), II.4.5, printed pp. 86–88.
