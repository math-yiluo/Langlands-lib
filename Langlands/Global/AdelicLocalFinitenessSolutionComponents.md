# Residual equations of the Harish-Chandra components of solutions of `Ξ_main`

Module `Langlands.Global.AdelicLocalFinitenessSolutionComponents`.

## Definitions (namespace `LocalFinitenessData`)

For data `X` of the system `Ξ_main` (module `AdelicLocalFinitenessStatement`), a predicate `J` on
the simple roots and directions `k`, which are either a simple root `β` with `¬ J β` or a central
index `j`:

- `X.dirDegree J k` is `X.degree β` for `k = β` and `X.centralDegree j` for `k = j`;
- `X.dirCoeff J s ε k` is the vector of lower coefficients of the residual polynomial on the
  orthant `ε`: those of `D_β(s)` for `k = β`; those of `D̃_j(s)` for `k = j` if `ε_j` is positive;
  and `D̃_j(s)_{m−q} / D̃_j(s)_0` (`m = X.centralDegree j`), the lower coefficients of the normalized
  reversal `D̃_j(s)(0)⁻¹ x^m D̃_j(s)(x⁻¹)`, if `ε_j` is negative.

## Results

- `residualFun_eq_zero_of_monic_of_natDegree`, `residualFun_inv_eq_zero_of_natDegree`: the residual
  lemmas of `AdelicLocalFinitenessComponentEquations` for a polynomial of a prescribed degree `m`
  (the degree of `D_β(s)` and `D̃_j(s)` is fixed by admissibility, while the coefficient vectors are
  indexed by `Fin m`).
- `StandardParabolicFamily.residualFun_hcComponent_eq_zero`: assume
  `PositiveTorusSplitComponentStatement` (as a hypothesis). Let `v ∈ 𝔉^R_L` be a solution of
  `Ξ_main(s)` for group data `(u, t, z)` of the family `𝓕` and admissible data `X`. For every finset
  `P` (index `J_P = P ∩ Δ`), orthant `ε` and direction `k`, the residual
  `residualFun (orthantShift a z J_P ε k) (X.dirCoeff J_P s ε k) (𝓕.hcComponent P v)` vanishes, where
  `a_β = i(t_β)` and `z_j = i(z_j)` and the orthant shift is `a_β`, `z_j` or `z_j⁻¹`.

  Proof. For a root `β ∉ J_P`, the hypothesis identifies `a_β` with the image of a point of the
  positive split component of the standard parabolic with index `Δ ∖ {β}`. The constant-term
  equation of `Ξ_main` for `β` is the difference equation of `D_β(s)` for the constant term along
  that parabolic (`subgroupConstantTerm_eq_constantTerm` with the group data clause on `u_β`).
  Since `J_P ⊆ Δ ∖ {β}`, `isTranslationPolynomialSolution_hcComponent` transfers it to
  `𝓕.hcComponent P v`, and monicity gives the residual equation. For a central index `j`, the
  hypothesis identifies `z_j` with a point of the positive split component of `G`
  (`constantTerm_top`), the central equation of `Ξ_main` transfers likewise, and the residual
  vanishes for `z_j` (monic `D̃_j(s)`) and for `z_j⁻¹` (nonzero constant coefficient, normalized
  reversal).

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), 187–234: §7.6, p. 219 (the components of a solution of `Ξ_main(s)` satisfy
`D_α(s)(T_{a_α})(f_P^S) ≡ 0` for `α ∉ Δ_0^P`) and §7.7, pp. 220–221 (the central equations
`D̃_i(s)^{ε_i}(T_{z_i}^{ε_i}) f^ε = 0` with the normalized reversed polynomial `D^−` on negative
orthants) (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`). The
equations here use raw left translation, as in the system of the Library statement.
