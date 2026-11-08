# A monomial gamma factor and a monomial dual integral give a constant corank-one integral

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement` (Jacquet–Shalika 1985,
§4.4, printed pages 329–330: with (15) and the choices (16)–(18), the functional equation
of the pair `(σ ⊗ χ, τ)` turns (14) into the right-hand side of (13)). This project applies
the published functional equation to the pair `(σ̃ ⊗ χ⁻¹, τ)` instead, with the internal
test vector of `KirillovShell` in place of their `W'`.

- `forward_eq_const_of_monomial'`: the statement of `forward_eq_const_of_monomial`
  (ConstantForward) with a dual constant `c_d : ℂ` that may vanish. If `c_d = 0`, the dual
  continuation is the zero rational function (uniqueness of continuations). The functional
  equation and `C X^N ≠ 0` then force the forward continuation to vanish on the half-plane.
- `corankOne_eq_const_of_gamma_monomial`: let `Π` be a representation of `GL_(m+2)` and `τ` one
  of `GL_(m+1)` over a p-adic field with its canonical structures, with a certificate
  `IsPadicPairGammaFactor F ψ ν Π τ G` and `G = rationalEpsilonMonomial C N`. Take nonzero
  functionals `ℓ` (standard character) and `ℓ''` (inverse character) and model vectors
  `f`, `W''`. Suppose the dual corank-one integral
  `corankOneIntegral (ψ.scale (-1)) abv μ (firstDualFunction f) (secondDualFunction W'')`
  equals `c_d (q^(-s))^(-N)` on a right half-plane. Then there is a minus-one scalar `ζ` of the
  model of `τ` (`HasModelMinusOneScalar τ ℓ'' ζ`) such that, on a right half-plane,
  `corankOneIntegral ψ abv μ f W'' s = (ζ^(m+1))⁻¹ C⁻¹ c_d q^N`. Here `μ` is the published
  `unipotentQuotientHaar`.
  The certificate is unfolded exactly as in `gamma_eq_of_adjacent_tests` (AdjacentComparison):
  `isPairGammaFactor_of_lt`, the published canonical compatible measure, the only block
  `j = k = 0`, and the published identifications `Padic.corankOneIntegral_eq_zeroZero` and
  `Padic.adjacentRank_dualUnequalRankIntegral_eq_corank`.
