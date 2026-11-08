# Character integrals over integral rows

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4: Fourier inversion of the weight `φ₁` in the passage from (14)
to (13), printed pages 329–330). The canonical topology, valuation and Borel structure of the
p-adic field are local instances.

- `HasIntegerConductorAt F ψ`: `ψ` is trivial on `O`, and for non-integral `t` some integral `z`
  gives `ψ(z t) ≠ 1`.
- `integral_integer_character`: `∫ ψ(t y) 1_O(t) dη(t)` is `η(O)` if `y` is integral and `0`
  otherwise, by the published `subgroup_character_integral_of_trivial` and
  `subgroup_character_integral_of_nontrivial`.
- `addChar_finset_sum`: additive characters turn finite sums into products.
- `integerCharacterFactor`, `integral_row_character`, `integrable_integerCharacterFactor`,
  `integrable_row_character`: the row integral `∫ ∏_j ψ(x_j u_j) 1_O(x_j) dx` over the
  published rectangular measure `rectangularMeasure η 1 (m+1)` (a product of copies of `η`) is
  `∏_j η(O) [u_j ∈ O]`, by Mathlib's `integral_fintype_prod_eq_prod`.
- `prod_integerCharacterFactor`: the row product equals `ψ(Σ_j x_j a_j)` on integral rows and
  `0` elsewhere.
- `integral_restrictedFourier_character`: for the finite exponential sum
  `S₂(ξ) = Σ_(z ∈ T) Φ(z) ψ(Σ_k z_k ξ_k)` restricted to integral `ξ`,
  `∫ S₂(rev x) ψ(Σ_j v_j x_j) dx = Σ_(z ∈ T) Φ(z) ∏_j η(O) [z_(rev j) + v_j ∈ O]`.
  When `T` represents distinct cosets of `O^(m+1)`, the right side is `η(O)^(m+1)` times the value
  of `Φ` at the class of `-rev v`.
