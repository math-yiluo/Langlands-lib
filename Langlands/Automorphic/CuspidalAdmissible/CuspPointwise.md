# The pointwise square-mean estimate for a unipotent translate in the cusp

Module: `Langlands.Automorphic.CuspidalAdmissible.CuspPointwise`. Provenance: internal; it
follows the inductive step of the Library's `blockDecay_of_cuspidal`
(`Langlands.Automorphic.CuspidalL2.Decay`), with the mean value estimate replaced by its
square-mean form `enorm_sub_sq_le_lintegral_squareZero`.

- `norm_sum_mul_sq_le`, `enorm_sum_mul_sq_le`: `‖∑ c_k v_k‖² ≤ (∑ |c_k|)² ∑ ‖v_k‖²`.
- `exists_cusp_pointwise K n h L hL Q hQ` (namespace `Langlands.Global`): for a block
  `h : a + b = n`, an open subgroup `L` of the finite adelic group and a compact `Q`, there are
  a compact set `𝒲` of archimedean block matrices and `B` such that for every adelic block
  `Y` some archimedean block `W_∞` (depending only on `Y`) has `s · W_∞ ∈ 𝒲` for
  `s ∈ [0, 1]`, and for every function `φ` that is rationally left invariant, right invariant
  under `L`, with smooth archimedean slices whose `lieDirection k` derivatives are the slices
  of `dφ k`, every `x`, `ℓ ≥ 0` with all across-the-block gaps `x_r - x_p ≤ -ℓ` and every
  `q ∈ Q`:

  `|φ(u(Y) A_x q) - φ(A_x q)|² ≤ (e^{-ℓ} B)² ∫_{[0,1]} ∑_k |dφ_k(u_∞(s W_∞) A_x q)|² ds`,

  with `A_x = ofInfinite (torInf x)` and `u_∞(V) = ofInfinite (blockUnipotent h V)`.
  Proof: finite absorption (`exists_nsmul_conj_blockUnipotent_mem`) gives `δ`;
  `Y = ξ + δ W` (`exists_matrix_decomposition`); the rational part is removed by left
  invariance and the finite part of `u(δW)` by the level; the archimedean part commutes past
  the torus as `u(s W_∞) A_x = A_x u(s Y')` (`torInf_inv_mul_blockUnipotent_mul`) with
  `Y' = e^{-ℓ} Y''`, `Y'' ∈ 𝒲`; with `Zm = conjNilpotent q_∞ Y'` (square zero),
  `φ(u(Y) A_x q) = s₀(X₀(1 + Zm))` for the slice `s₀` at the finite part of `q`. The square-mean
  estimate, the expansion `smoothDifferential_val_eq_sum` in `lieBasis`, the coefficient bound
  `∑_k |coeff_k(Zm)| ≤ e^{-ℓ} B` (compactness of `𝒲 × Q`, `conjNilpotent_smul`) and
  `enorm_sum_mul_sq_le` give the inequality; the points `X₀(1 + s Zm)` are
  `u_∞(s W_∞) A_x q`.
