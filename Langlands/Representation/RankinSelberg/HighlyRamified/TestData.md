# The test data of Jacquet–Shalika (4.4.4), (4.4.6)–(4.4.8), (4.4.18)

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement` (Jacquet–Shalika 1985,
§4.4, printed pages 328–331). The test vector (4.4.4) is built from a test function `Φ` on
`F × F^(m+1)`. In the Library it is a finite sum `Σ_(z ∈ T) Φ(z) ρ(n(z)) W₀`
(`candidateTest`, DualValue). Here `T = T₁ × T₂` and `Φ(u, z) = Φ₁(u) Φ₂(z)`, where `Φ₂` is the
weight (4.4.18) (`dualWeight`, DualWeight) and `Φ₁` comes from `exists_unit_inversion`
(UnitInversion).

## Powers of the maximal ideal (any field with a valuative relation)

`InPow.mono` (`𝔭^c ⊆ 𝔭^f` for `f ≤ c`), `InPow.mul` (`𝔭^a 𝔭^b ⊆ 𝔭^(a+b)`), `InPow.pow`
(`ϖ ∈ 𝔭 ⇒ ϖ^c ∈ 𝔭^c`) and `InPow.zero_of_integral` (`O = 𝔭^0`).

## Products

- `productTest T₁ T₂`: the image of `T₁ ×ˢ T₂` under `(u, z) ↦ Fin.cons u z`.
  `productWeight Φ₁ Φ₂ z = Φ₁(z₀) Φ₂(tail z)`. `cons_injective_pair`: the map is injective.
- `finiteFourier_product`: the finite Fourier transform (`finiteFourier`, DualValue) of the
  product weight over the product set is
  `(Σ_(u ∈ T₁) Φ₁(u) ψ(u ξ₀)) · (Σ_(z ∈ T₂) Φ₂(z) ψ(Σ_k z_k ξ_(k+1)))`. This is the factorization
  hypothesis `hfac` of the dual reduction (DualReduction).

## Condition (4.4.8)

`dualWeight_fourier_eq_zero` (canonical structures): assume `ψ` has conductor `O`, `f ≥ 1`,
`ω` is trivial on `1 + 𝔭^f`, `ϖ ∈ 𝔭` is nonzero and `c ≥ 2f`. Let `T₂ ⊆ ϖ^(-c) O^(m+1)` be
representatives of `ϖ^(-c) O^(m+1) / O^(m+1)`. Then for integral `v` with some `v_k ∉ 𝔭^f`,
`Σ_(z ∈ T₂) Φ₂(z) ψ(Σ_k z_k v_k) = 0`. Proof: pick `δ = z ϖ^(f-c) e_(k₀)` with
`ψ(δ_(k₀) v_(k₀)) ≠ 1`, using the conductor property. `Φ₂` is invariant under `δ`
(`unitLastWeight_add`). Translating the representatives by `δ` (`sum_reps_shift`,
UnitInversion, with the product Haar measure on `F^(m+1)`) multiplies the sum by
`ψ(δ_(k₀) v_(k₀))`. Hence the sum vanishes.

## The `I`-side condition (4.4.19)–(4.4.21)

`productTest_isDeepFirstRow`: let `T₁ ⊆ ϖ^(-b) O`, `ϖ ∈ 𝔭` and `c ≥ f + b`. At every point of
`productTest T₁ T₂` where `productWeight Φ₁ (dualWeight ω ϖ c f)` does not vanish, the first row
`z` satisfies `IsDeepFirstRow f z` (ISide): `z_last ≠ 0`, `1/z_last ∈ 𝔭^f` and
`z_j / z_last ∈ 𝔭^f` for `j < last`. With `d = ϖ^c z_last` a unit, `1/z_last = ϖ^c d⁻¹`,
`u / z_last = (ϖ^b u) ϖ^(c-b) d⁻¹` and `z_j / z_last = (ϖ^c z_j) d⁻¹`. This is the argument on
printed page 331 of the source, with `c = a(r-1)` and the exponent `-c+f` of (4.4.18).
