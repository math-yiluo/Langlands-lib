# Comparing adjacent-rank gamma factors through test vectors

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4, printed page 327, equation (4.4.1)).

`gamma_eq_of_adjacent_tests` takes two candidates `π₁, π₂` of `GL_(n+2)` and a test
`σ` of `GL_(n+1)` over a p-adic field with its canonical structures, with existing
certificates `IsPadicPairGammaFactor F ψ ν πᵢ σ Gᵢ`. Suppose there are nonzero
Whittaker functionals `ℓ₁, ℓ₂` and a nonzero inverse-character functional `ℓ'`, and
model vectors `f₁, f₂, f'` such that

- the corank-one integrals `Ψ(s, fᵢ, f')` (measure `unipotentQuotientHaar`) agree on a
  right half-plane, and
- the dual corank-one integrals of `(f̃ᵢ, f̃')`, for `ψ⁻¹`, both equal one nonzero
  constant `c` on a right half-plane.

Then `G₁ = G₂`.

The proof unfolds both certificates to `UnequalRankGammaEquation` for the canonical
compatible quotient measure and the chosen functionals, at the only block `j = k = 0`
of adjacent ranks. The minus-one scalars of the common test model coincide by
`HasModelMinusOneScalar.unique`. The published identifications
`Padic.corankOneIntegral_eq_zeroZero` and
`Padic.adjacentRank_dualUnequalRankIntegral_eq_corank` turn the block-zero integrals
into the corank-one integrals above. Rational-continuation uniqueness makes both
forward continuations one function `R` and both dual continuations the constant `c`
(`hasRationalContinuation_const_of_eventually`). `R ≠ 0`: otherwise the functional
equation at a real point where the denominator of `G₁` does not vanish (finitely many
exceptions, `finite_spectralPoint_roots`) gives `c = 0`. Finally
`GammaFunctionalEquation.gamma_unique` gives `G₁ = G₂`.
