# Unfolding along nested discrete subgroups; Haar measure under automorphisms

Module `Langlands.Global.EisensteinConstantTerm.QuotientUnfolding`. This is abstract measure
theory used in the proof of Bernstein–Lapid (6.17). It covers the exchange of the sum over
`(U_Q ∩ wU_{P_w}w⁻¹)(F) \ U_Q(F)` with the integral over `U_Q(F) \ U_Q(𝔸)`, and the
substitution `u ↦ γ u γ⁻¹` for `γ ∈ Q(F)` (BL, proof of Lemma 6.10, journal p. 208, PDF
page 22).

## Results

- `lintegral_out_eq`: for a quotient measure `LeftCosetSpace.quotientMeasure Γ ν s` (push-forward
  of `ν` restricted to `s`) and a measurable left `Γ`-invariant `f : H → ℝ≥0∞`,
  `∫⁻ q, f(q̄) = ∫⁻_{x ∈ s} f x dν`, where `q̄ = Quotient.out q`. This is the lower-integral
  analogue of the Library's `RankinSelbergGlobal.Unfolding.integral_out_eq`. It is proved
  through `LeftCosetSpace.lift` and `lintegral_map`.
- `isFundamentalDomain_iUnion_smul`: let `Λ ≤ Γ`, let `t` be a measurable strict fundamental
  domain of `Γ` (`∀ x, ∃! γ, γ x ∈ t`), and let `ρ` be countably many representatives of
  `Λ \ Γ`. Then `⋃ i, ρ_i t` is a fundamental domain of `Λ`. The Library's
  `existsUnique_mem_iUnion_smul` supplies the uniqueness.
- `lintegral_unfold`: with the same data, a left-invariant `μ` and a measurable left
  `Λ`-invariant `f : H → ℂ`,
  `∫⁻_{Λ \ H} ‖f(x̄)‖ₑ = ∫⁻_{v ∈ t} ∑'_i ‖f(ρ_i v)‖ₑ dμ`. Here `Λ \ H` carries the quotient
  measure built on `⋃ ρ_i t`. The proof is `lintegral_out_eq`, then `lintegral_iUnion` (the
  translates are disjoint by the Library's `pairwise_disjoint_smul`), then the change of
  variables `x = ρ_i v`, and finally `lintegral_tsum`.
- `integral_unfold`: if the right side of `lintegral_unfold` is finite, then `x ↦ f(x̄)` is
  integrable on `Λ \ H`, `v ↦ ∑'_i f(ρ_i v)` is integrable on `t`, and
  `∫_{Λ \ H} f(x̄) = ∫_{v ∈ t} ∑'_i f(ρ_i v) dμ`. It combines the finiteness from
  `lintegral_unfold` with the Library's `integrableOn_tsum_and_setIntegral_eq`,
  `integrable_out_iff` and `integral_out_eq`.
- `existsUnique_mem_preimage`: let `α` be a group automorphism with `α x ∈ Γ ↔ x ∈ Γ`. The
  preimage under `α` of a strict fundamental domain of `Γ` is again one.
- `map_eq_self_of_preserves`: let `H` be locally compact, second countable and Borel, `Γ`
  countable, `s` a measurable strict fundamental domain of `Γ` with `0 < μ s < ∞` for the Haar
  measure `μ`, and `α : H ≃ₜ* H` with `α(Γ) = Γ`. Then `α_* μ = μ`.
  - Proof: `α_* μ` is a Haar measure, so it equals `c • μ` (Mathlib
    `isMulLeftInvariant_eq_smul`). Both `s` and `α⁻¹ s` are fundamental domains of `Γ`, so
    `μ(α⁻¹ s) = μ s` (`IsFundamentalDomain.measure_eq`). Hence `c μ s = μ s`, and `c = 1`.
- `measurePreserving_of_preserves`: the same for any multiple `c • μ`.

## Provenance

BL justify the substitution `u ↦ γuγ⁻¹` by the normalization of the Haar measure. In the
statement's Markdown this is the product formula. The proof here uses neither: it uses only that
`α` preserves the lattice `Γ`, which has a fundamental domain of finite positive measure. The
unfolding is the standard one (BL p. 208, third display; MW II.1.7, printed pp. 91–93). The
formalization is internal.
