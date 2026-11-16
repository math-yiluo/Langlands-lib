# The radical `Y_(n,m)` as `𝔸^((m+1)×K) ⋊ N_K`

Module `Langlands.Global.RankinSelberg.DualExpansionRadical`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal. `Y_(n,m) = projectionUnipotent F n m` (`n = m + K + 1`) consists of the
upper unitriangular matrices whose first `m + 1` columns are those of the identity (Library
`mem_projectionAdelic_iff`).

## Coordinates

- `yMat A` (rows `≤ m`, columns `≥ m + 1`) and `yPoint A = 1 + yMat A`; `brMat U = diag(I_(m+1), U)`
  (built from `lrMatrix (m+1) K`), `brGL`, `brPoint u`; `brSub M` is the bottom-right `K × K`
  block, multiplicative on matrices whose lower-left block vanishes (`brSub_mul`).
- `YGroup F m K`, the adelic points of `Y_(n,m)`, with `yPoint_mem` and `brPoint_mem`.
- Homomorphisms `yHom : ColGroup F (Fin (m+1) × Fin K) →* YGroup F m K`,
  `brHom : N_K(𝔸) →* YGroup F m K` and `blockHom : YGroup F m K →* N_K(𝔸)` with
  `blockHom_brHom`, `blockHom_yHom`, `exists_yHom_eq`, continuity, `isEmbedding_yHom`, and
  compatibility with rational points (`mem_rationalY_iff`, `brHom_mem_rational`,
  `blockHom_mem_rational`, `yHom_mem_rational_iff`).

## The coefficient

**`coefficient_eq_iterated`**: for `ψ` continuous and trivial on `F` and a continuous function
`f` on `GL_n(𝔸)`, left invariant under `GL_n(F)`, the Library's character coefficient along
`Y_(n,m)` with `projectionCharacter` equals
`UP_K (u ↦ T_A f(yPoint A · brPoint u · x) · conj χ(yPoint A · brPoint u))`. The proof applies
the Library's `subgroupCharacterCoefficient_eq_setIntegral` and
`LeftCosetSpace.Semidirect.normalizedPeriod_eq_iterated_of_compact` to the splitting above, and
`normalizedPeriod_ratLattice` to the abelian factor.
