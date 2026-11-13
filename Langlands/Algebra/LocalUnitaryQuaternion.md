# Quaternion division algebras with unitary involutions over local fields: the descent case

Helper module for the proof of `Langlands.LocalUnitaryDivisionCommutativeStatement`.

Setting: nonarchimedean local fields `K` and `L` with `[Algebra K L]`, `[L : K] = 2`, valuations
compatible (`hKL`: `valuation L (algebraMap a) ≤ valuation L (algebraMap b) ↔
valuation K a ≤ valuation K b`); `σ : L →+* L` fixing exactly `K` (`hσK`, `hfix`) and moving some
`θ`; `D` central division over `L` of reduced degree `2` with a unitary involution `τ`.

* `exists_fixed_unit_conj_nontrivial`: there are a unit `U` of `D` with `β U = U` and `w ∈ D`
  with `v_D w ≤ 1` and `¬ v_D (U w U⁻¹ - w) < 1`. Apply `exists_unit_conjResidue_faithful` to the
  central division `K`-algebra `D₀` (`Langlands.Algebra.QuaternionUnitaryDescent`): since
  `reducedDegree K D₀ = 2` does not divide `1`, some unit `u₀` of `D₀` acts nontrivially on the
  residue field of `D₀`, i.e. some integral `w₀` has `v_{D₀}(u₀ w₀ u₀⁻¹ - w₀) = 1`. By `nrd_fixed`
  and `hKL`, for `y ∈ D₀` the conditions `v_D y ≤ 1` and `v_D y < 1` are equivalent to the same
  conditions for `v_{D₀} y`; take `U = u₀`, `w = w₀`.
* `false_of_valuation_squares` (**ramified case**): if every nonzero `c ∈ K` satisfies
  `valuation L c = (valuation L ℓ)²` for some nonzero `ℓ ∈ L`, contradiction. With `U` as above,
  `σ (Nrd U) = Nrd (β U) = Nrd U`, so `Nrd U = c ∈ K`, and `v_D U = valuation L (Nrd U) =
  (valuation L ℓ)² = v_D ℓ`. By `conjResidue_eq_of_value_eq`, conjugation by `U` acts on the
  residue field like conjugation by the central element `ℓ`, i.e. trivially, contradicting the
  choice of `w`.
