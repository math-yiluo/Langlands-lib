# Lemma II.3.1 for the standard block parabolic subgroups of `GL_n`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SigmaProductGL`, namespace
`Langlands.HarishChandraSchwartz`. It imports `SigmaProduct` (`IsBlockDiagonal`,
`IsBlockUnipotent`, `sigmaProductBound_height`) and the Library module
`Langlands.Group.GL.Blocks` (Worker 6: `BlockShape`, `BlockShape.indexEquiv`,
`BlockShape.leviSubgroup`, `BlockShape.unipotentSubgroup`, `BlockShape.parabolic`, and the
entry lemmas `leviEmbedding_apply_ne`, `mem_parabolic_iff`, `mem_unipotentSubgroup_iff`).
Through `SigmaProduct` it uses `height` and `glNorm` of `Height` and `SigmaProductBound` of
`ConstantTermBound`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, Lemma II.3.1 (printed pp. 254–255, PDF pp. 20–21): for a
semi-standard `P = M U`,
`C_1 (1 + σ(m u)) ≤ 1 + sup(σ(m), σ(u)) ≤ C_2 (1 + σ(m u))`. In its proof `τ` is
conjugated so that `τ(M)` lies in a block diagonal Levi `M'` and `τ(U)` in the block upper
unipotent radical `U'` of a block upper triangular parabolic `P'` of `GL_n`.

## Scope

This is a `GL_n`-specific instance. Here `G = GL_n(F)` (`GeneralLinear n F`) for a normed
field `F` with an ultrametric absolute value and `n ≥ 1`, with the standard embedding
`τ = id`, so `σ = height (MonoidHom.id _)` is `log` of the largest absolute value of an entry
of `g` or `g^{-1}` (Waldspurger's `σ` for this embedding). For an ordered block shape `B`
of `n`, `P = M U` is the standard block upper triangular parabolic of the Library, with `M`
the block diagonal matrices and `U` the block upper unitriangular matrices. In this case
the block form of II.3.1 holds already for `τ` itself (no conjugation is needed), so the
lemma is proved without hypotheses. The opposite parabolic `M Ū`, other embeddings `τ`, and
semi-standard parabolics other than the standard block ones are not treated.

## Shared coordinate definition

- `BlockShape.coordinateBlock B i`: the block of the coordinate `i ∈ Fin n` (the first component of
  `B.indexEquiv.symm i`), reused from `Langlands.Group.GL.Blocks`.

## Results

- `glBlock_indexEquiv`: `B.coordinateBlock (B.indexEquiv ⟨p, a⟩) = p`.
- `isBlockDiagonal_of_mem_leviSubgroup`: every `m ∈ B.leviSubgroup F` satisfies
  `IsBlockDiagonal (B.coordinateBlock) m`.
- `isBlockUnipotent_of_mem_unipotentSubgroup`: every `u ∈ B.unipotentSubgroup F`
  satisfies `IsBlockUnipotent (B.coordinateBlock) u`: below the diagonal blocks its entries vanish
  (it lies in the parabolic) and its diagonal blocks are identity matrices.
- `sigmaProductBound_glBlock` (Lemma II.3.1 for `GL_n`):
  `SigmaProductBound (B.leviSubgroup F) (B.unipotentSubgroup F) (height (MonoidHom.id _))`.

## Proof notes

The two block-form lemmas read the entries in block coordinates through
`B.indexEquiv`: off-diagonal blocks of the Levi embedding vanish
(`leviEmbedding_apply_ne`); blocks strictly below the diagonal of a parabolic element vanish
(`mem_parabolic_iff`), and the diagonal blocks of a unipotent element are identity matrices
(`mem_unipotentSubgroup_iff`); distinct block coordinates are distinct indices since
`B.indexEquiv` is injective. The lemma is then `sigmaProductBound_height` with `x = 1`.
