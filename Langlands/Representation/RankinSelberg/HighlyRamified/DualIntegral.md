# Separating the last diagonal coordinate in a quotient integral

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4, the integration over `t` in formula (5), printed page 328).

`integral_separate_last m η` uses the published disintegration
`lowerBlockQuotientDisintegration` of the canonical quotient measure
`unipotentQuotientHaar F (m+1)` on `N_(m+2) \ GL_(m+2)` along lower-block coordinates with
one final row: `([A], x, c) ↦ [[[A,0],[x,c]]]`, with `[A] ∈ N_(m+1) \ GL_(m+1)`,
`x ∈ F^(1 × (m+1))` (rectangular Haar measure from `η`) and `c` in the lower triangular
group of `GL_1`. The disintegration supplies a σ-finite measure `ρ` on that group, a positive
constant `C`, and the density `lowerBlockQuotientDensity (m+1) 1 = |det A|⁻¹`.

The theorem states: there are such `ρ` and `C` that for every measurable `f` on the quotient
and every `κ` with `f(chart(q,x,c)) = κ(c) f(chart(q,x,1))`,
`∫ f = C · (∫ κ dρ) · ∫ f(chart(·,·,1)) d(μ_(m+1)·|det|⁻¹ × dx)`.
No integrability is assumed. If `f` is not integrable, the published equivalence of
integrability through the chart shows that both sides vanish. Otherwise the disintegration
identity, the associativity equivalence `MeasurableEquiv.prodAssoc` and the product formula
`integral_prod_mul` give the separation.

`integral_separate_last_iterated m η` is the iterated form: if moreover `κ` is measurable with
`0 < ∫⁻ ‖κ‖ dρ < ∞` and `f` is integrable, then
`∫ f = C (∫ κ dρ) ∫ |det A|⁻¹ (∫ f(chart([A],x,1)) dx) dμ_m([A])`. Integrability of
`(q,x) ↦ f(chart(q,x,1))` on `μ_m|det|⁻¹ × dx` follows from that of `f` by the published
integrability transfer and `lintegral_prod_mul`; Fubini (`integral_prod`) and
`integral_withDensity_eq_integral_toReal_smul` then give the iterated integral.
The statement also records the published bounds `0 < ρ(K) < ∞` for compact open subgroups.
