# Cells of the two-block parabolic relative to the upper unitriangular group

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingCells` (namespace
`Langlands.Global.CuspidalPairEisenstein`) specializes the orbit decomposition of
[CuspidalPairEisensteinRowEchelon.md](CuspidalPairEisensteinRowEchelon.md) to the upper
two-block parabolic `P = blockShape r t` of `GL_N`, `N = r + t + 2`, with blocks of sizes
`r + 1` and `t + 1`. It also supplies the matrix facts needed for the vanishing of the non-open
cells. This is the two-block `GL_N` analogue of the double coset decomposition (2.10.2)–(2.10.3)
in Shahidi, *Functional equation satisfied by certain L-functions*, Compositio Math. 37
(1978), proof of Lemma 2.1, pp. 181–182. Shahidi works with a split group `G` of type `G₂`. He
writes `U` for the unipotent radical of a fixed Borel subgroup (§1, p. 173), and `P = MN` for a
maximal parabolic subgroup containing it, with unipotent radical `N` (§2, p. 176). There the
double cosets `U_F \ G_F / P_F` of (2.10.2) are indexed through the Bruhat decomposition by the
classes `w ∈ W/W_M` in (2.10.3), p. 182. For the two-block parabolic of `GL_N` the counterpart
of Shahidi's `U` is the upper unitriangular group, called `N₀` here, and the counterpart of his
`N` is the unipotent radical of `P`, called `U` here. The double cosets are indexed by pivot
sets `J`, with permutation matrices as representatives. The source works with the right
quotient `G_F/P_F`. The Library takes the left quotient `P(F) \ GL_N(F)`, which corresponds to
it under inversion `g ↦ g⁻¹`.

## Block shape

- `mem_blockShape_parabolic_iff`: `g ∈ (blockShape r t).parabolic R` exactly when
  `g i j = 0` for `i ≥ r + 1` and `j < r + 1`.
- `mem_blockShape_unipotentSubgroup_of`: a matrix equal to the identity outside the upper right
  block (`i < r + 1 ≤ j`) lies in the unipotent radical `U`.

## Cell representatives

- `exists_perm_mem_iff`: for `J` of size `n - a` there is a permutation `σ` with `j ∈ J` exactly
  when `σ j ≥ a`. `lowerRowSpace_permutation`: the rows `≥ a` of the permutation matrix of such a
  `σ` span `coordSpace J`.
- `openPivots r t = {j | j < t + 1}` (`card_openPivots`: it has `t + 1 = N - (r + 1)`
  elements) is the open cell `J₀`. `openCellPermutation` is the Library's
  `Shahidi.blockWeylPermutation (r + 1) (t + 1)`, reindexed to size `N`. It is the permutation
  of the block Weyl representative of Shahidi, *Fourier transforms of intertwining operators and
  Plancherel measures for GL(n)*, Amer. J. Math. 106 (1984), p. 72, (0.2).
  `openCellWeyl_eq_permutation`: `openCellWeyl F r t` is its permutation matrix.
- `cellPermutation r t J` is `openCellPermutation` for `J = J₀`, and otherwise a permutation
  from `exists_perm_mem_iff`. `cellRep r t F J` is its rational permutation matrix `γ_J`.
- `rational_cellRep_openPivots`: the adelic image of `γ_(J₀)` is `openCellWeyl F r t`, the block
  Weyl representative `w = [[0, I_(r+1)], [I_(t+1), 0]]` of
  [CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md).
- `cellOrbitMap_bijective`: `(J, Λ_J δ) ↦ P(F) γ_J δ` is a bijection from
  `Σ J : PivotIndex N (r + 1), StabilizerCosets J` onto `P(F) \ GL_N(F)`. It is
  `orbitMap_bijective` with `mem_blockShape_parabolic_iff` and `lowerRowSpace_permutation`.

## Non-open cells

- `exists_simpleRoot_of_ne_openPivots`: a subset `J` of size `t + 1` other than `J₀` contains
  `k + 1` but not `k` for some `k`. Otherwise the complement of `J` is closed under
  successors. If some `j ≤ t` were missing from `J`, then `J ⊆ {0, …, j - 1}` would have fewer
  than `t + 1` elements. So `J₀ ⊆ J`, and the cardinalities give `J = J₀`.
- `rootElement k k' hk y = 1 + y E_(k,k')`, with `rootElement_mem_upperUnipotent` for `k < k'`
  and `rootElement_mem_stabilizer` for `k ∉ J`, `k' ∈ J`.
- `sum_superdiag_rootElement`: for `k' = k + 1` the superdiagonal entries of `1 + y E_(k,k+1)`
  sum to `y`.
- `permutation_conj_mem_parabolic`: if `σ` moves `J` onto the coordinates `≥ r + 1`, then
  `σ Λ_J σ⁻¹ ⊆ P`.
- `permutation_conj_rootElement_mem`: for such `σ`, `g ∈ Λ_J`, `k ∉ J` and `k' ∈ J`, the
  conjugate `σ (g (1 + y E_(k,k')) g⁻¹) σ⁻¹` lies in the unipotent radical `U` of `P`. By
  `conj_rootElement_apply`, the entries of `g (1 + y E_(k,k')) g⁻¹ - 1` are
  `g_(p,k) y (g⁻¹)_(k',q)`. They vanish for `p ∈ J`, because `k ∉ J`, and for `q ∉ J`, because
  `k' ∈ J` and `g⁻¹ ∈ Λ_J`. After conjugation by `σ`, the only entries that can be nonzero
  have row `< r + 1` and column `≥ r + 1` (`permutation_conj_rootElement_apply`).

Over `R = 𝔸` these facts give the averaging identity behind the vanishing of a non-open cell `J`
([CuspidalPairEisensteinUnfoldingCellIntegral.md](CuspidalPairEisensteinUnfoldingCellIntegral.md)).
Take `k ∉ J` with `k + 1 ∈ J`, `y₀ ∈ 𝔸` with `ψ(y₀) ≠ 1`, and `v₀ = 1 + y₀ E_(k,k+1) ∈ Λ_J(𝔸)`.
For fixed `x ∈ N₀(𝔸)`, right translation of `n ∈ Λ_J(𝔸)` by `v₀` multiplies the function
`n ↦ cellIntegrand J (n x)` by `conj(ψ(y₀)) ≠ 1`. This is the block-matrix version of Shahidi's
vanishing argument in the paragraph after (2.10.3), p. 182. There `V = wPw⁻¹ ∩ U` and
`V_w = U ∩ wNw⁻¹`, and the integral over `V_𝔸 / V_F` factors through the character integral
`∫_{(V_w)_𝔸 / (V_w)_F} conj(χ(u)) du`, which vanishes when `V_w` is nontrivial. So only the
class of the open cell survives. Here the root group of `(k, k + 1)` lies in the analogue
`N₀ ∩ γ_J⁻¹ U γ_J` of `V_w`: by `permutation_conj_rootElement_mem` with `g = 1`,
`γ_J v₀ γ_J⁻¹` lies in the unipotent radical `U` of `P`. The implementation chooses
this one simple root, on which `ψ_N` is nontrivial, and proves the vanishing by Weil averaging
over `Λ_J(F) \ Λ_J(𝔸)` (`setIntegral_eq_zero_of_mul_right`,
[CuspidalPairEisensteinUnfoldingVanishing.md](CuspidalPairEisensteinUnfoldingVanishing.md)).
