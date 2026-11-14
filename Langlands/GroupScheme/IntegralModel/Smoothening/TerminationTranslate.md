# Termination of the smoothening sequence: reducedness of Hopf algebras by translation

Author: Worker 348. Internal helper module for the final step of Kaletha–Prasad, Theorem A.6.2.
The argument is internal to this project. It uses the homogeneity of a group under translations by
its points.

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`.

Setting: `k` is a field and `H` is a commutative Hopf algebra over `k`, in the same universe.
`rtrans` (right translation by a point, `TerminationGamma`) is applied over the base `k`.

- `conv φ ψ = (φ ⊗ ψ) ∘ Δ` is the convolution of two points (`conv_apply`).
- `apply_rtrans`: `ψ (rtrans φ c) = conv ψ φ c`.
- `rtrans_rtrans`: `rtrans ψ ∘ rtrans φ = rtrans (conv ψ φ)`. Both sides are expressed through
  `(Δ ⊗ id) Δ` and `(id ⊗ Δ) Δ`, which agree by coassociativity (`Coalgebra.coassoc_apply`).
- `conv_comp_antipode` and `conv_antipode_comp`: `g ∘ S` is a two-sided convolution inverse of a
  point `g`. They use Worker 50's `lift_id_antipodeAlgHom_comp_comul` and
  `lift_antipodeAlgHom_comp_comul`.
- `exists_algHom_of_ne_top` (**Nullstellensatz**): if `k` is algebraically closed and `H` is
  finitely generated, every proper ideal lies in the kernel of a `k`-point. Choose a maximal ideal
  `M`. Then `H ⧸ M` is a finite extension of `k` (Zariski's lemma,
  `finite_of_finite_type_of_isJacobsonRing`), and `IsAlgClosed.lift` maps it to `k`.
- `isReduced_of_forall_sq_eq_zero` (**reducedness by translation**): suppose `k` is algebraically
  closed, `H` is finitely generated, and every `f` with `f² = 0` lies in every power of the
  augmentation ideal `m`. Then `H` is reduced.

  Proof: it suffices that `f² = 0` implies `f = 0` (`isReduced_iff_pow_one_lt`). Suppose `f ≠ 0`.
  - The annihilator of `f` is proper, so it lies in the kernel of a point `g`.
  - The translate `rtrans g f` has square zero, so it lies in every `m^i`.
  - The Krull intersection theorem (`Ideal.mem_iInf_smul_pow_eq_bot_iff`, `H` Noetherian) gives
    `r ∈ m` with `(1 - r) · rtrans g f = 0`.
  - Translate back by `a = g ∘ S`: `rtrans a (rtrans g f) = f`. Hence `u = rtrans a (1 - r)`
    annihilates `f`.
  - But `g u = conv g a (1 - r) = ε(1 - r) = 1`, a contradiction.
