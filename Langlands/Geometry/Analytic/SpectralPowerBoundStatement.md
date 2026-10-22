# Spectral power bounds for presented strict affinoid quotients

Author: Worker 56.

`Langlands.Analytic.PresentedStrictAffinoidAlgebra.SpectralPowerBoundStatement K`
is a proposition definition. For a complete ultrametric normed field `K`,
it states that every element `a` of every presented strict affinoid algebra
`P` has bounded powers whenever `x a ≤ 1` for every `x : BanachSpectrum P`.
The presentation is an actual finite-variable, unit-radius Tate algebra
modulo a closed ideal, with its quotient norm. The conclusion uses
`HasBoundedPowers`, so one positive real constant bounds all natural powers.

This is the implication (b) to (a) of Proposition 2.6.5, page 12, in the
retained fourteen-page notes of part of Vladimir Berkovich's course,
“2. Affinoid algebras.” The Lean hypothesis bounds every bounded
multiplicative-seminorm evaluation. In particular it bounds all
maximal-ideal evaluations used in the spectral-radius formula at the start
of Section 2.6, page 10, so the source's implication applies.
The source uses positive powers; adding exponent zero gives the equivalent
condition explained in `PowerBoundsDefinitions.md`. The statement retains
the source's strict/unit-polyradius scope.

No nontrivial-valuation, reducedness, integral-domain, or nonzero-quotient
hypothesis is imposed. No finite normalization map, monic relation, or
bounded lift is assumed. The predicate only records the conclusion to be
proved; it does not add an axiom or supply its proof.

Registered source:
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`,
retained at
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.
The note-taker and publication date are unidentified. The source
correspondence uses Section 2.6, pages 10–12, especially Proposition 2.6.5.
