# Rectangle periods and the dual period

Module `Langlands.Global.RankinSelberg.DualExpansionRectangle`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal. The dual period is the period, over `V(F) \ V(𝔸)` with
`V = (X ⊕ C) ⋊ N_K` (rectangle `X` of size `K × m`, column `C` of size `K`, middle block `N_K`),
of a corner sum against the character `ψ(superdiagonal of u + last entry of c)`. It is the
group-theoretic form of the extra unipotent integration in the dual unfolding of
Cogdell 2004, §2.2, printed p.207 (PDF p.210).

## Rational points

- `xcRat ρ` and `xcPoint_rat_eq_padRational`: a rational rectangle point is a padded rational
  corner element; `xcPoint_zero_eq_lastColPoint` and `xcPoint_rat_split` split rational
  `xcPoint`s, and `midPoint_rat_eq_padRational` does the same for rational middle blocks.
- Consequently `cornerSum` and `cornerNormSum` are invariant under left multiplication by
  rational `xcPoint`s and rational `midPoint`s (`DualData.cornerSum_xcPoint_rat_mul`,
  `DualData.cornerSum_midPoint_rat_mul` and the norm versions).

## Definitions

- `rectPeriod F m K ψ G g = T_(x ∈ (𝔸/F)^(K×m)) T_(c ∈ (𝔸/F)^K) ψ(lastEntry c) G(x̂ ĉ g)`.
- `dualPeriod F m K ψ W y = UP_K (u ↦ ψ(superSum u) · rectPeriod (cornerSum W) (diag(I, u, 1) y))`.

## Analysis

- Continuity of `xcMat`, `xcPoint` (jointly and in each argument), `lrMatrix` and `midPoint`.
- `midPoint_inv_conj`: conjugating `x̂ĉ` by a middle block.
- `DualData.exists_bound`: for fixed `y`, `cornerNormSum W (x̂ ĉ · diag(I,u,1) · y)` is bounded
  uniformly in `x`, `c` and `u ∈ N_K(𝔸)`. The proof reduces `u` (Library
  `exists_isCompact_unitriangular_reduction`) and `x`, `c` (Library
  `exists_isCompact_algebraMap_add_mem`) into compact sets by rational translations, under which
  the norm sum is invariant, and uses continuity on the compact set.
