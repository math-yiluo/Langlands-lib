# Invariants of finite-dimensional `𝔤𝔩_n(ℂ)`-modules with integral weights

Module `Langlands.Representation.Archimedean.GLReynolds`, namespace
`Langlands.Archimedean.GLReynolds`. It imports the Library module `ComplexJacquetFinite` for
`IsGlFamily`, and Mathlib's `𝔰𝔩₂` theory (`Mathlib.Algebra.Lie.Sl2`).

This module is the first part of a planned proof of Kostant's multiplicity bound
(`VermaGL.KostantMultiplicityStatement`, Library module `LowerVerma`). The later parts use it
to turn equivariant maps into a finite-dimensional module into equivariant maps into
`U(𝔤𝔩_n(ℂ))`. It contains no Library statement and proves only the results listed below; no
new axioms are used.

## Setting

All results are stated for a family `e : Fin n → Fin n → Module.End ℂ V` of operators on a
complex vector space `V`, rather than for a Lie algebra representation.

* `IsGlFamily e` (Library, `ComplexJacquetFinite`): the commutation relations
  `[e_ab, e_cd] = δ_bc e_ad - δ_da e_cb` of the matrix units of `𝔤𝔩_n`.
* `IsWeightVec e μ v` (`μ : Fin n → ℤ`): `e_pp v = μ_p v` for all `p`.
* `IntWeights e`: `V` is spanned by such weight vectors with integral weights.
* `cas e = Σ_{p,q} e_pq e_qp`, the Casimir operator.

## Results

* `cas_comm`, `cas_apply_comm`, `cas_pow_apply_comm`: the Casimir operator and its powers
  commute with every `e_ab`. This is a direct computation from `IsGlFamily`.
* `exists_lowest`: a nonzero finite-dimensional `V` with `IntWeights e` contains a lowest
  weight vector: a nonzero weight vector killed by all `e_pq` with `q < p`. The heights
  `ht μ = Σ_r r μ_r` of the weights of nonzero weight vectors are eigenvalues of
  `H = Σ_r r e_rr`, so there are finitely many. Take a nonzero weight vector of greatest height.
  For `q < p`, `e_pq` maps a weight vector of weight `μ` to one of weight `μ + ε_p - ε_q`, of
  height `ht μ + (p - q)` (`isWeightVec_shift`, `ht_shift`), so it kills that vector.
* `sl2_nat`, `sl2_rel`: for `p ≠ q` the triple `(e_pp - e_qq, e_pq, e_qp)` satisfies the
  `𝔰𝔩₂` relations. Hence, in a finite-dimensional module, a nonzero `v` with `e_pq v = 0` and
  `(e_pp - e_qq) v = μ v` has `μ ∈ ℕ`. If `μ = 0`, then also `e_qp v = 0`. This uses Mathlib's
  `IsSl2Triple.HasPrimitiveVectorWith` (`exists_nat`, `pow_toEnd_f_eq_zero_of_eq_nat`). The
  degenerate case `e_pp - e_qq = 0` is handled separately.
* `cas_apply_lowest`: on a lowest weight vector `v` of weight `μ`,
  `c v = (Σ_p μ_p² + Σ_{q<p} (μ_p - μ_q)) v`. For `q < p`, `e_pq e_qp v = (μ_p - μ_q) v`, since
  `e_pq v = 0`; for `p < q`, `e_pq e_qp v = 0`.
* `exists_poly_eq_zero`, `apply_eq_zero_of_sq`: with integral weights each `e_pp` is
  annihilated by `X · Π_{k ∈ s} (X - k)` for a finite set `s` of nonzero integers. Hence
  `e_pp² v = 0` implies `e_pp v = 0`.
* `exists_invariant`: if moreover `c` is nilpotent and `V ≠ 0`, there is a nonzero invariant
  vector (killed by every `e_pq`). Let `v` be a lowest weight vector of weight `μ`. By
  `𝔰𝔩₂`, `μ_p - μ_q ∈ ℕ` for `q < p`. So the eigenvalue of `c` on `v` is a sum of nonnegative
  integers, and it vanishes because `c` is nilpotent. Hence `μ = 0`. Then the `𝔰𝔩₂` triple
  `(e_qq - e_pp, e_qp, e_pq)`, `q < p`, gives `e_qp v = 0`.
* `qFam`, `qFam_mk`, `isGlFamily_qFam`, `intWeights_qFam`, `cas_qFam_mk`, `cas_qFam_pow_mk`: the
  family induced on the quotient `V ⧸ S` by an `e`-stable subspace `S`. It again satisfies the
  relations and has integral weights; its Casimir operator is induced by `c`.
* `eq_zero_of_isNilpotent_cas` (via `eq_zero_of_isNilpotent_cas_aux`, strong induction on
  `finrank V`): if `V` is finite-dimensional with `IntWeights e` and `c` is nilpotent, then
  every `e_pq` is zero. Take a nonzero invariant `v₀` (`exists_invariant`) and apply the
  induction hypothesis to `V ⧸ ℂ v₀`. Then every `e_ab x` lies in `ℂ v₀` and is invariant, so
  `e_ab e_cd = 0`. For `p ≠ q`, the relation `e_pq = e_pp e_pq - e_pq e_pp` gives `e_pq = 0`.
  Finally `e_pp² = 0`, so `e_pp = 0` by `apply_eq_zero_of_sq`.
* `apply_mem_range_cas_pow`: every `e_pq` maps `V` into `range (c ^ N)`. Apply
  `eq_zero_of_isNilpotent_cas` to the quotient `V ⧸ range (c ^ N)`, on which `c` is nilpotent.
* `exists_invariant_lift` (**invariant lifting**): let `φ : V → W` be a surjective linear map
  between finite-dimensional spaces with `φ ∘ e_pq = f_pq ∘ φ`, where `e` satisfies the
  relations and has integral weights. Then every `y ∈ W` killed by all `f_pq` is `φ x` for
  some `x ∈ V` killed by all `e_pq`.
  Choose `N ≥ 1` with `V = ker cᴺ ⊕ range cᴺ` and `W = ker c_Wᴺ ⊕ range c_Wᴺ` (Mathlib's
  `eventually_isCompl_ker_pow_range_pow`); here `c_W` is the Casimir operator of `f`. Write a
  preimage of `y` as `k + r` with `k ∈ ker cᴺ` and `r ∈ range cᴺ`. Then `φ r` lies in
  `range c_Wᴺ`. It also lies in
  `ker c_Wᴺ`, because `c_W y = 0` and `φ k ∈ ker c_Wᴺ`. So `φ r = 0` and `φ k = y`. Finally
  `e_pq k` lies in `ker cᴺ` (commutation) and in `range cᴺ` (`apply_mem_range_cas_pow`), so it
  vanishes.

The argument is the standard Casimir proof of complete reducibility. It is specialized to
`𝔤𝔩_n(ℂ)` with integral weights, where the eigenvalue of `c` on a lowest weight vector is
visibly a sum of nonnegative integers.
