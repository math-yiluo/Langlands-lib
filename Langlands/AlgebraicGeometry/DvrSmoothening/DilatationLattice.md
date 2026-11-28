# The lattice comparison behind the defect drop under dilatation

Pure module theory over a discrete valuation ring `R` with uniformizer `ϖ`.

- `coeff_mem_maximalIdeal`: if `∑ cᵢ vᵢ ∈ ϖ F` and the `1 ⊗ vᵢ ∈ k ⊗ F` are linearly independent
  over the residue field `k`, then every `cᵢ` lies in the maximal ideal.
- `mem_span_of_smul_mem_span`, `linearIndependent_of_residue`: in a torsion-free module, a finite
  family with linearly independent images in `k ⊗ F` is linearly independent and spans a saturated
  submodule (`ϖ x ∈ span ⟹ x ∈ span`).
- `latticeMap ϖ bP b2 dz`: for bases `bP` of `F_P` indexed by a finite type `σ` and `b2` of `F₂`
  indexed by `σ ⊕ Fin n`, the map `θ₀ : F₂ → F_P` with `θ₀ (b2 (inl i)) = ϖ² bP i` and
  `θ₀ (b2 (inr j)) = ϖ dzⱼ`; `latticeMap_basis` computes it on the basis.
- `torsionLength_lt_of_presentations`: here `F_P` and `F₂` are free of finite rank (`σ` is a
  `Fintype`). Finite rank is needed: with infinite bases the quotients `F_P ⧸ N_P` and
  `F₂ ⧸ N₂` can both have infinite torsion length, and then the strict inequality fails. Let `α : F_P → F₂` send `bP i` to `b2 (inl i)`, let
  `(dz, dw)` be linearly independent with saturated span, `N_P ⊆ F_P` contain the `dwₗ`, and
  `N₂ ⊆ F₂` contain the `α dwₗ` and the `α dzⱼ − ϖ b2 (inr j)`. Assume every element of `N_P` is
  `θ₀ y` modulo the `dwₗ` for some `y ∈ N₂`, and every element of `N₂` is, after multiplication by a
  power of `ϖ`, of the form `α x` with `x ∈ N_P` modulo the elements just listed. If `F_P ⧸ N_P`
  has non-zero torsion, the torsion of `F₂ ⧸ N₂` is strictly shorter. The proof divides `F_P` by
  the span `W` of the `dwₗ` and `F₂` by the span `W₂` of the listed auxiliary elements. Since
  `θ₀ = ϖ θ₁` for the map `θ₁` with `θ₁ (b2 (inl i)) = ϖ bP i` and `θ₁ (b2 (inr j)) = dzⱼ`, the
  induced map `θ : F₂ ⧸ W₂ → F_P ⧸ W` has image in `ϖ`-multiples. It is injective modulo the
  auxiliary elements (`θ₀ v ∈ W` implies `v ∈ W₂`, using independence and saturation of
  `(dz, dw)`). With `N = N_P ⧸ W` and `N' = N₂ ⧸ W₂`, the first assumption gives `N ⊆ im θ` and,
  together with this injectivity, `θ⁻¹ N ⊆ N'`; the second assumption gives that `N'` lies in the
  saturation of `θ⁻¹ N`. `TorsionLength.torsionLength_lt_of_lattice` then applies, the quotients
  being identified with `F_P ⧸ N_P` and `F₂ ⧸ N₂` by the third isomorphism theorem.

In the application `F_P = R' ⊗ Ω_P` and `F₂ = R' ⊗ Ω_{P₂}` for presentations `P` of `A` and `P₂` of
the dilatation, and `θ₀` multiplies the coordinates transversal to the centre by `ϖ` and the other
coordinates by `ϖ²`. This replaces the comparison of Jacobian minors in Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §3.3, proof of Proposition 5 (printed pp. 70–71).
