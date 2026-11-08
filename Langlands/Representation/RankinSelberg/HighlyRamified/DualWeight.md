# The weight of Jacquet–Shalika (4.4.18)

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. Source:
H. Jacquet and J. A. Shalika, *A lemma on highly ramified ε-factors*, Math. Ann. 271 (1985),
§4.4, formula (18), printed page 330. There `φ₁(x, y) = ω⁻¹(d)` for `x ∈ F^(r-3)`, `y ∈ F`
if `x ≡ 0` modulo `𝔭^(-a(r-1)+f)`, `y = ϖ^(-a(r-1)) d` and `|d| = 1`, and `φ₁ = 0` otherwise.
Here `r = m + 3`, `x` stands for the first `m` coordinates and `y` for the last one. With
`c = a(r-1)` the exponent is `-c+f`, and this module uses it directly, written as a function
of `ϖ^c z`. Here `f` is the level of the subgroup `K⁰(f)` of `DualTarget`, and `c` and `f`
are arbitrary natural numbers in the Lean definitions.

- `InPow f x`: `x` lies in `𝔭^f`, i.e. it is the image of an element of the `f`-th power of the
  maximal ideal of the integer ring. `IsIntegralUnit x`: `x ≠ 0` and `x`, `x⁻¹` are integral.
  The lemmas `InPow.add`, `InPow.neg`, `InPow.sub`, `InPow.integral_mul`, `InPow.integral`
  record the ideal properties.
- `isIntegralUnit_of_mul_eq`: if `a b = 1 + y` in the integer ring with `y` in the maximal
  ideal, then `b` is an integral unit (`1 + y` is a unit of the local ring).
  `IsIntegralUnit.add_inPow`: an integral unit plus an element of `𝔭^f`, `f ≥ 1`, is an
  integral unit.
- `unitLastWeight ω f v`: `ω(v_last)⁻¹` if `v_i ∈ 𝔭^f` for every `i ≠ last` and `v_last` is
  an integral unit, and `0` otherwise. `dualWeight ω ϖ c f z := unitLastWeight ω f (ϖ^c z)`.
  This is the source's `φ₁(z)`: `ϖ^c z_i ∈ 𝔭^f` is `z_i ∈ 𝔭^(-c+f)` for a uniformizer `ϖ`, and
  `ϖ^c z_last = d` is the unit of the source.
  `unitLastWeight_of_cond` and `unitLastWeight_of_not_cond` unfold it.
- `unitLastWeight_add`: if `ω` is trivial on `1 + 𝔭^f` (`TrivialOnPrincipalUnits`, from
  `DualTarget`) and `f ≥ 1`, then `φ` is invariant under translation by `(𝔭^f)^(m+1)`. The
  value uses the published-style congruence lemma `omega_eq_of_sub_mem`.
  `dualWeight_add`: hence `Φ₂` is invariant under translation by `O^(m+1)` whenever
  `ϖ^c O ⊆ 𝔭^f`.
- `IsIntegralMatrix k`: `k` and `k⁻¹` have integral entries. `inFirstColumn_iff`: `k ∈ K⁰(f)`
  iff `k ∈ GL_(m+1)(O)` and `k_(j,0) ∈ 𝔭^f` for `j ≠ 0`.
- `unitLastWeight_firstColumn`: for `k ∈ GL_(m+1)(O)`, the weight at
  `v_i = -(k⁻¹)_(rev i, 0)` is `ω(-1)⁻¹ ω(k₀₀)` if `k ∈ K⁰(f)` and `0` otherwise. The
  conditions on `v` say that `k⁻¹ ∈ K⁰(f)`, and `K⁰(f)` is a group. The value uses
  `(k⁻¹)₀₀ k₀₀ ≡ 1` modulo `𝔭^f` (`firstColumn_entry_unit`). The source states without details,
  on printed page 330, that with these choices the right-hand side of (14) reduces to the
  right-hand side of (13). This lemma is the internal step of that reduction in which the
  dual integrand becomes supported on the subgroup `K⁰(f)`, whose first column is congruent
  to `(*, 0, …, 0)`.
