# Equivariance of the dual Whittaker factor under the first-column line subgroup

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4: the replacement of `F` by its average `F_0` in formula (11) and the
evaluation after (12), printed pages 328–329). There `W_(i,0)` transforms under `K_r(f)` by
`ω_f`; here the corresponding statement is proved from invariance under the published level
subgroup and the central character.

- `InFirstColumn f k`: `k` lies in the first-column line subgroup at `𝔭^f` (`FirstColumnLine`).
- `integer_of_mem_pow`: elements of `𝔭^f` are integral.
- `firstColumn_entry_unit`: for such `k`, `(k⁻¹)_(0,0) k_(0,0) ≡ 1` modulo `𝔭^f`. Indeed
  `1 = (k⁻¹ k)_(0,0) = (k⁻¹)_(0,0) k_(0,0) + Σ_(l≠0) (k⁻¹)_(0,l) k_(l,0)`, and each `k_(l,0)` with `l ≠ 0` lies in `𝔭^f`.
- `firstColumn_entry_isUnit`: for `f ≥ 1`, `k_(0,0)` is nonzero, integral, with integral
  inverse, since `(k⁻¹)_(0,0) k_(0,0)` is `1` plus an element of the maximal ideal.
- `scalar_mul_apply`, `mul_scalar_apply`: entries of products with scalar matrices.
- `scalar_mul_dualConj_mem_levelSubgroup`: for `f ≥ 1`, `k_(0,0) · M(diag(k,1))` lies in the level-`f`
  subgroup, by the published entry criterion (`mem_levelSubgroup_of_entries`). The entries of
  `M(diag(k,1))` are those of `diag(k⁻¹,1,1)` at reversed positions. Its last row is the reversed first column of
  `diag(k⁻¹,1,1)`, which is `(k⁻¹)_(·,0)`; after the scalar factor this is `e_last` modulo `𝔭^f`.
- `whittaker_dualConj_firstColumn`: if `W` is right invariant under the level-`f` subgroup and
  `W(z g) = ω(z) W(g)` for scalars `z`, then `W(g · M(diag(k,1))) = ω(k_(0,0))⁻¹ W(g)` for
  `k ∈ K⁰(f)`, `f ≥ 1`. In particular `Ξ(A) = W(M(diag(A,1)))` satisfies
  `Ξ(A k) = ω(k_(0,0))⁻¹ Ξ(A)`, because `M` is multiplicative.
