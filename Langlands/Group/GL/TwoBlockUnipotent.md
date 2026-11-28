# The unipotent radical of a two-block parabolic subgroup

The module `Langlands.Group.GL.TwoBlockUnipotent` studies the unipotent radical
`U = B.unipotentSubgroup R` of the standard block parabolic subgroup of `GL_n(R)` for a block
shape `B` with two blocks (`B.length = 2`). It shows that `u ↦ δ⁻¹ u⁻¹ δ u` is an automorphism of
`U` when `δ` is block diagonal with blocks of coprime characteristic polynomials. The block
shapes, parabolic subgroups, Levi embedding and unipotent radicals are those of the module
`Langlands.Group.GL.Blocks`.

## Strictly upper block triangular matrices

`B.IsStrictUpper X` means that `X (B.index i a) (B.index j b) = 0` whenever `j ≤ i`, so all
entries of `X` in the blocks on or below the block diagonal vanish. For any block shape over a
commutative ring this condition is closed under sums, negatives, differences and scalar
multiples (`isStrictUpper_zero`, `IsStrictUpper.add`, `.neg`, `.sub`, `.smul`). The theorem
`mem_unipotentSubgroup_iff_isStrictUpper` shows that `g ∈ U` exactly when `g - 1` is strictly
upper block triangular. It follows from the Library's `mem_unipotentSubgroup_iff` and
`mem_parabolic_iff`.

For a two-block shape:

- `IsStrictUpper.mul_eq_zero`: the product of two strictly upper block triangular matrices is
  `0`. A nonzero product entry would need a middle coordinate in a block strictly after the
  first block and strictly before another block, and there are only two blocks.
- `unipotentOfStrictUpper`: for such `X`, the matrix `1 + X` is invertible with inverse `1 - X`.
  It lies in `U` (`unipotentOfStrictUpper_mem`). For `u ∈ U` the inverse is
  `1 - (u - 1)` (`inv_val_of_mem_unipotentSubgroup`).
- `mul_comm_of_mem_unipotentSubgroup`: `U` is commutative, since `u v = (u - 1)(v - 1) + u + v - 1`
  and the product term vanishes.

## The automorphism `u ↦ δ⁻¹ u⁻¹ δ u`

Let `F` be a field, `m : B.Levi F` and `δ = B.leviEmbedding F m`. Assume the blocks of `m` have
pairwise coprime characteristic polynomials.

- `IsStrictUpper.levi_conj`: `δ X δ⁻¹` is strictly upper block triangular when `X` is. This
  follows from the Library's `levi_conj_mem_unipotentSubgroup` (module
  `Langlands.Group.GL.OppositeBlocks`) applied to `1 + X`.
- `strictUpper F` is the subspace of strictly upper block triangular matrices, and
  `twistLinear hB m` is the `F`-linear map `X ↦ X - δ⁻¹ X δ` on it.
- `twistLinear_injective`: if `X = δ⁻¹ X δ`, then `δ` commutes with `1 + X`. By the Library's
  `mem_leviSubgroup_of_commute` (module `Langlands.BaseChange.LeviNormDescent`; this is where
  coprimality is used), `1 + X` is block diagonal (`mem_leviSubgroup_iff_offBlock_eq_zero`).
  Its blocks above the diagonal are those of `X`, so `X = 0`. `twistLinear_surjective` follows
  because the subspace is finite-dimensional (Mathlib's `LinearMap.injective_iff_surjective`).
- `twistHom hB m : U →* U` is `u ↦ δ⁻¹ u⁻¹ δ u`. It takes values in `U` because the Levi
  subgroup normalizes `U`, and it is multiplicative because `U` is commutative. In the
  coordinate `X = u - 1` it is `twistLinear` (`twistHom_sub_one`): with `Y = δ⁻¹ X δ`,
  `δ⁻¹ (1 - X) δ (1 + X) = (1 - Y)(1 + X) = 1 + X - Y`, since `Y X = 0`. Hence it is
  injective and surjective (`twistHom_injective`, `twistHom_surjective`), and `twistMulEquiv`
  is the resulting group automorphism of `U`.
- `twistContinuousMulEquiv`: let `F` be a Hausdorff topological field whose general linear group
  `GL_n(F)` is locally compact and σ-compact. Then the automorphism is a homeomorphism. It is
  continuous (`continuous_twistHom`). `U` is closed (`isClosed_unipotentSubgroup`), so it is
  locally compact, σ-compact and a Baire space. Mathlib's open mapping theorem
  `MonoidHom.isOpenMap_of_sigmaCompact` then makes the continuous bijective homomorphism open.

## Origin

The decomposition `u = 1 + X` of the unipotent radical of a maximal parabolic subgroup, with
`X` in the abelian Lie algebra of `k × (n - k)` blocks, is standard. So is the bijectivity of
`X ↦ X - Ad(δ⁻¹) X` when the two diagonal blocks of `δ` have no common eigenvalue (Sylvester's
theorem on the equation `a X = X d`). Here bijectivity is derived from the Library's
centralizer statement `mem_leviSubgroup_of_commute` and finite dimensionality, not from
Sylvester's theorem. The automorphism is the change of variables `u ↦ δ⁻¹ u⁻¹ δ u` on `U` used
in the proof of `CuspFormOrbitalVanishingStatement` (module
`Langlands.BaseChange.CuspFormOrbitalVanishing`). It identifies `∫_U f(x⁻¹ u⁻¹ δ u y) du` with
`∫_U f(x⁻¹ δ v y) dv'` for the transported Haar measure `dv'`, which is an integral along a
two-sided translate of `U`.
