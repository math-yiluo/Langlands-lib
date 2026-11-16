# Conjugating the radical into the dual period group

Module `Langlands.Global.RankinSelberg.DualExpansionConj`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal. With `w = diag(I_m, w_(K+1))` (the Library's `unfoldingWeyl`, see module
`DualExpansionFinal`), the map `y ↦ w ᵗy⁻¹ w` sends `Y_(n,m)` onto the group
`V = {x̂ ĉ · diag(I, u, 1)}` of the dual period. This is the form in which the extra unipotent
integration of the dual integral (Cogdell 2004, §2.2, printed p.207) enters the proof.

- `wPerm` (the involution fixing `0, …, m-1` and reversing `m, …, m+K`), its permutation matrix
  `wMat`, `wGL` and the adelic point `wPoint`, with `wPoint_mul_wPoint`, the conjugation formula
  `pointMatrix_wPoint_conj` and rationality `wPoint_mem_rationalSubgroup`.
- `pointMatrix_iota`: entries of the transpose inverse; `yPoint_inv`, `brPoint_inv`.
- `rectX A (i, j) = -A(j, K-1-i)` and `rectC A i = -A(m, K-1-i)`.
- **`wPoint_iota_conj`**: `w · ι(yPoint A · brPoint u) · w = xcPoint (rectX A) (rectC A) ·
  midPoint (dualConj u)`, from `wPoint_iota_yPoint` and `wPoint_iota_brPoint`
  (`dualConj` is the Library's `u ↦ w_K ᵗu⁻¹ w_K`, with entries `pointMatrix_dualConj`).
- Characters: `conj χ(yHom A) = ψ(lastEntry (rectC A))` and
  `conj χ(brHom u) = ψ(superSum (dualConj u))` (`conj_projectionCharacter_yHom`,
  `conj_projectionCharacter_brHom`), using `sum_superdiag_brMat` and `superSum_dualConj`
  (Library `sum_superdiag_dualConjGL`).
