# Proof of the gamma normalization statement

Worker 216. This module proves the published Library statement
`Langlands.RankinSelberg.GammaNormalizationStatement` (module
`Langlands.Representation.RankinSelberg.GammaNormalizationStatement`) as the
theorem `Langlands.RankinSelberg.gammaNormalization`.

## Statement proved

For every `q : ℕ` with `1 < q`, every `ζ : ℂˣ`, `e : ℕ`,
`G : RationalFunctions`, sets `S T : Set RationalFunctions` and polynomials
`P Pdual : ℂ[X]` with `IsNormalizedGenerator S P` and
`IsNormalizedGenerator T Pdual`: if every `R ∈ S` has some `Rdual ∈ T` with
`GammaFunctionalEquation q ζ e G R Rdual`, and every `Rdual ∈ T` has some
`R ∈ S` with that equation, then there are `c : ℂˣ` and `m : ℤ` such that every
pair `R Rdual : RationalFunctions` satisfying
`GammaFunctionalEquation q ζ e G R Rdual` also satisfies
`NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual`.

## Proof

The statement is, binder for binder, the type of
`Langlands.RankinSelberg.gammaNormalization_of_incidence` in the helper module
`Langlands.Representation.RankinSelberg.GammaNormalizationAlgebra`. The proof
introduces the binders and applies that theorem. The algebraic argument is
described in `GammaNormalizationAlgebra.md`: reflection `X ↦ q⁻¹/X` preserves
Laurent coefficients, the two incidences identify the generated modules after
reflection and multiplication by `ζ^e G`, the normalized generators therefore
differ by a Laurent unit, which is a nonzero monomial, and the monomial
identity is evaluated without evaluating `G`, so the full reduced-denominator
domain is kept.

## Provenance

This is the derived algebraic part of the normalization in Jacquet,
Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions* (1983), §2.9,
printed pp.395-396, where the gamma factor is divided by the two L-factors and
the quotient is shown to be a monomial `ε(s)`. It is internal derived content,
not a verbatim source statement.
