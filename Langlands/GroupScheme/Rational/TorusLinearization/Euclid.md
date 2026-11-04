# Frobenius bases of spaces of additive polynomials

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
Internal machinery only.

- `frobSpan₁ A p m`: the span of `X ^ (p ^ r)` for `r ≥ m` in one variable. `frobSpan A p m S`:
  the span of the `g ^ (p ^ r)` with `g ∈ S` and `r ≥ m`. Membership is equivalent to being a sum
  `Σ_g aeval g ψ_g` with `ψ_g ∈ frobSpan₁` (`exists_eq_sum_of_mem_frobSpan`).
- Left division of additive one-variable polynomials over a field `k` of characteristic `p`
  (`IsAddPoly₁.exists_comp_add`): for additive `h ≠ 0` and additive `φ`, there is an additive `ψ`
  with `φ = ψ.comp h + ρ`, where `ρ` is additive and `deg ρ < deg h`. This is the Euclidean
  algorithm in the twisted polynomial ring `k{F}`.
- `exists_frobBasis`: let `N` be a `k`-subspace of additive polynomials that is closed under
  `p`-th powers. Then `N` has a finite subset `G` such that `N ≤ frobSpan k p 0 G` and `G` is
  `FrobIndep`: no nontrivial relation `Σ_g aeval g ψ_g = 0` with additive `ψ_g`. The proof is by
  induction on the set of variables that occur. Each step takes an element of minimal degree in
  the image of the projection `part j` and divides by it.
- `FrobIndep.eq_zero_of_sum_smul_mem`: if `G` is `FrobIndep` and `Σ c_g • g` lies in the span of
  the `p`-th powers of `G`, then all `c_g` vanish.

These results say that `N` is a free left module over `k{F}`, where `F` acts by `p`-th powers.
They are the usual Euclidean-division argument in the twisted polynomial ring.
