# The dual matrices of the corank-one dual integral

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4, the integral `J_i` of formula (3), printed page 327).

The dual corank-one integral evaluates the first dual function `F̃(x) = F(w ᵗx⁻¹)` at
`diag(h, 1)` for `h ∈ GL_(n+1)(F)`. Writing `w` for the long Weyl element of `GL_(n+2)`:

- `dualConj h = w · ᵗdiag(h,1)⁻¹ · w` (`dualConj_apply`). It is a group homomorphism
  `GL_(n+1) → GL_(n+2)`, since `w² = 1` (published `weylLong_mul_self`).
- `dualConj_entry`: `M(h)_(i,j) = (diag(h,1)⁻¹)_(rev j, rev i)`, by the published
  conjugation formula for `w` and the entries of the inverse transpose.
- `dualConj_inv_entry`: `(M(h)⁻¹)_(i,j) = diag(h,1)_(rev j, rev i)`, since `M(h)⁻¹ = M(h⁻¹)`.
- `dualConj_col_zero`: the first column of `M(h)` is `e_0`, because the last row of
  `diag(h,1)⁻¹` is `e_last`. So `M(h) = diag(1, w ᵗh⁻¹ w)`-type matrices satisfy the
  hypothesis of `whittaker_mul_firstRowUnipotent`.
- `dualConj_inv_succ_one`: `(M(h)⁻¹)_(k+1, 1) = h_(last, rev k)`. This is the coordinate
  through which the first-row unipotent translations of the test vector act on the dual side.
