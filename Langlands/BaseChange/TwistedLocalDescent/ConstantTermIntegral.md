# The integral of the twisted constant term over a subset of the Levi

Module `Langlands.BaseChange.TwistedLocalDescent.ConstantTermIntegral`.

`integral_indicator_twistedConstantTerm`: let `μU` be a Haar measure on the radical
`B.unipotentSubgroup E` with `μU(U ∩ K) = 1` and `μK` the Haar probability measure on
`K = GL_n(𝒪_E)`. For a measurable `S ⊆ M(E)` and a test function `φ`, the normalized twisted
constant term `φ^{P,σ}` (the Library's `normalizedTwistedParabolicConstantTerm E B σ φ`) satisfies

`∫_S φ^{P,σ}(x) dx = ∫_K Φ(k) dk`, `Φ(k) = ∫_P 1_S(p_M) δ_P(p)^{1/2} φ(k⁻¹ p σ(k)) dp`,

with `dp = dm du` (`parabolicHaar`).

Proof: by `normalizedTwistedParabolicConstantTerm_apply_unipotentSubgroup` both sides are
iterated integrals of
`f(m, u, k) = 1_S(m) δ_P(m)^{1/2} φ(k⁻¹ m u σ(k))` over `M × U × K` in different orders.
`f` is integrable: it is measurable and dominated by the continuous function
`δ_P(m)^{1/2} |φ(k⁻¹ m u σ(k))|`, which has compact support (as `k` runs over the compact `K`,
`m u` stays in the compact set `{k z σ(k)⁻¹ : k ∈ K, z ∈ supp φ} ∩ P`, and `M × U ≃ P` is a
homeomorphism). Fubini on `(M × U) × K` and the definition of `parabolicHaar` conclude.
