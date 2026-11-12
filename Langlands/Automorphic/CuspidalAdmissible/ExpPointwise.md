# Pointwise estimate along archimedean exponential curves

Module: `Langlands.Automorphic.CuspidalAdmissible.ExpPointwise` (namespace
`Langlands.Global`). Provenance: internal; the fundamental theorem of calculus along a
one-parameter subgroup, in the form used for the compact part of the joint admissibility
proof.

- `exists_lieBasis_coeff_bound K n`: there is `Cb ≥ 0` with `∑_k |c_k(Z)| ≤ Cb ‖Z‖` for the
  coordinates `c_k` of an archimedean matrix `Z` in the fixed basis `lieBasis` (each coordinate
  functional is a continuous linear map; `le_opNorm`).
- `exists_exp_pointwise K n`: there is `Cb ≥ 0` such that for every `φ` on `GL_n(𝔸)` and
  continuous `dφ_k` such that the archimedean slices `g ↦ φ(ofInfinite g · ofFinite y)` are
  smooth with `lieDirection k` derivatives the slices of `dφ_k`, every `x` and every real Lie
  direction `Y`,

  `|φ(x · exp Y) - φ(x)|² ≤ (Cb ‖Y‖)² ∫_[0,1] ∑_k |dφ_k(x · exp(tY))|² dt`.

  Proof: write `x = ofInfinite(a) · ofFinite(y)`; the slice `s` at `y` satisfies
  `d/dt s(a exp(tY)) = ∑_k c_k(Y) dφ_k(x exp(tY))` (`hasDerivAt_smooth_oneParameter`,
  `smoothDifferential_val_eq_sum`). The fundamental theorem of calculus gives the difference as
  the integral of this derivative over `[0, 1]`; then `‖∫ D‖ ≤ ∫ ‖D‖`, Jensen on the unit
  interval (`sq_lintegral_le`), and `|∑ c_k v_k|² ≤ (∑ |c_k|)² ∑ |v_k|²`
  (`enorm_sum_mul_sq_le`) with the coordinate bound.
