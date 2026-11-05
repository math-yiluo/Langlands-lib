# Convergence and local domination of standard integrals from quotient decay

Lean module: `Langlands.Representation.Plancherel.CompactIntertwiningQuotientDecay`. The
majorant form of the Iwasawa reduction is in `Langlands.Plancherel.StandardIntertwining`; the
decay predicate and its two consequences are in `Langlands.Plancherel`.

## Purpose and provenance

Provenance: internal. In Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), IV.1, printed pp. 277–279 (PDF pp. 43–45), absolute convergence
of the standard intertwining integral over `(U ∩ U') \ U'`, locally uniformly in the twisting
character, is deduced from moderate growth of coefficients and a decay estimate for the Levi
component of the Iwasawa decomposition. This module isolates that deduction. It names the
decay estimate as an explicit predicate, `IsLocallyUniformQuotientDecayOn`, and proves that
the predicate, an integrable function `W` and a coefficient envelope give

- full scalar convergence of every twist on the parameter set (`scalarDomain … = ⊤`), and
- the local integrable domination `CompactIntegralLocallyDominatedOn` used by the published
  rationality assembly (`ParabolicIntertwiningAssembly`, `ParabolicPointUniformNumerator`).

The decay estimate itself is not proved here. The arguments are derived from published
results and are not transcribed from the source.

## Setting and notation

The ambient group `G` is locally compact and nonarchimedean, with actual subgroups `P`, `M`,
`U`, a decomposition `h : IsSemidirectDecomposition P M U`, closed `U` (`hU`) and any subgroup
`U'`. `QuotientSpace (U := U) U'` is the actual left quotient `(U ∩ U') \ U'`; `Quotient.mk _ u'`
is the coset of `u' ∈ U'`. `K` is an open subgroup, and in the domination result also
compact with `G = P K` (`hPK`). `ν : I → (M →* ℝ≥0ˣ)` defines the unramified characters
`unramifiedCharacters ν`, a subgroup of continuous characters `M →ₜ* ℂˣ`; `χ.val m` is the value
at `m`. `δ(m)` is the published half modulus
`HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m`. `A` is a complex smooth
representation of `M`. `iwasawaWeight h hU U' ξ p` is the published weight
`q ↦ ‖δ(m(p q))‖ * ξ (m(p q))`, with `m = h.projection`.

## Declarations

- `StandardIntertwining.scalarDomain_eq_top_of_le_integrable`: the hypotheses of the published
  `scalarDomain_eq_top_of_integrable_iwasawaWeight` (compact `K`, a nonnegative envelope `ξ`
  bounding all coefficients of `A` up to constants, coordinates `p`, `k` with
  `u' = p q * k q` for some representative `u'` of each `q`), but with the integrability of the
  weight replaced by an integrable `W` with `iwasawaWeight h hU U' ξ p q ≤ W q` for all `q`.
  Conclusion: `scalarDomain h hU U' A ν = ⊤`.
- `IsLocallyUniformQuotientDecayOn h hU K ν U' σ ξ W Ω` (definition, a `Prop`), for
  `σ : QuotientSpace (U := U) U' → U'`, `ξ : M → ℝ`, `W` a real function on the quotient and
  `Ω` a set of unramified characters: for every `χ₀ ∈ Ω` there are a neighbourhood `N` of `χ₀`
  in `unramifiedCharacters ν` and `C : ℝ` such that for every `χ ∈ N`, every quotient point `q`
  and every `p ∈ P`, `κ ∈ K` with `σ q = p κ` in `G`,
  `‖δ(m)‖ * (‖χ(m)‖ * ξ m) ≤ C * W q` with `m = h.projection p`.
- `scalarDomain_twist_eq_top_of_quotientDecay`: assume `K` compact, `G = P K`, `ξ ≥ 0` a
  coefficient envelope for `A`, `σ` a section of the quotient map (`hσ`), `W` integrable for a
  Borel quotient measure `qν`, and `IsLocallyUniformQuotientDecayOn … σ ξ W Ω`. Then for every
  `χ ∈ Ω`, `scalarDomain h hU U' (A.twist χ …) qν = ⊤`.
- `compactIntegralLocallyDominatedOn_of_quotientDecay`: under the same hypotheses, with the
  remaining data of the published compact pictures (`hδ` unimodularity of `U`, `hP`, `hν`,
  `hr`), `CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK ν hν hr A U' qν Ω`.

## Proofs as implemented

**Majorant form.** As in the published proof: reduce to the identity evaluation point
(`scalarDomain_eq_top_iff_integrable_at_one`), take the uniform constant `C` of the published
`scalarIntegrand_bound`, and apply `Integrable.mono'` to `C * W`, using the published strong
measurability of scalar integrands. At `q`, the factorization `u' * 1 = p q * k q` of the
chosen representative gives `‖ℓ (integrand …)‖ ≤ C * weight q ≤ C * W q`.

**Scalar convergence.** Choose, for each `q`, a factorization `σ q = p q * κ q` (`hPK`). The
twist `A.twist χ` has envelope `m ↦ ‖χ(m)‖ * ξ m` (published `coefficientEnvelope_twist`). With
`N`, `C` from the decay predicate at `χ₀ = χ` (and `χ ∈ N`), the twisted weight is at most
`C * W q`, so the majorant form applies to `C * W`.

**Domination.** Fix a compact section `f`, a point `k ∈ K`, a smooth functional `ℓ` and
`χ₀ ∈ Ω`. The section is locally constant on the compact `K`, so its values `v κ` form a finite
set, and choosing coefficient constants for `ℓ` gives one bound `C₁ = max 1 B` with
`‖ℓ (A(m) (v κ))‖ ≤ C₁ * ξ m` for all `κ` and `m`. Take `N`, `C` from the decay predicate at
`χ₀`, and the bound `q ↦ C₁ * (C * W q)`, which is integrable. For `χ ∈ Ω` near `χ₀` (the
preimage of `N` under the subtype inclusion is a neighbourhood) and any `q`, factor
`σ q = p κ`. The integrand at `q = [σ q]` is the extended section at `σ q * k = p (κ k)`, which by
the published `unramifiedLeviInductionCompactEquiv_symm_mul` equals
`δ_P(p) • (χ(m) • A(m) (v (κ k)))`. With `U` unimodular, published
`closedHalfCharacter_eq_comp_projection` gives `δ_P(p) = δ(m)`. Hence
`‖ℓ (integrand)‖ ≤ ‖δ(m)‖ ‖χ(m)‖ C₁ ξ(m) ≤ C₁ C W q`.

## Scope

The decay predicate and the integrability of `W` are hypotheses. For the actual groups of the
conditional intertwining statement, `σ` can be the inverse opposite chart and `W` a negative
power of the height (as in the separate candidate module `ParabolicOppositeQuotient`); proving the decay predicate on the
region of that statement requires the root-cone estimate and is not done here. No rational
continuation, squared-modulus identity or completion of the host theorem is claimed.
