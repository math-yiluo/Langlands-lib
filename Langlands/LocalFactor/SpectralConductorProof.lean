import Langlands.LocalFactor.SpectralConductorReduction
import Langlands.LocalFactor.SpectralConductorRankOneProof
import Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof

/-!
# Tate's spectral conductor formula for supplied local-constant systems

Tate, *Number theoretic background* (1979), (3.4.5), and Deligne (1973), (5.5.2), at the
bottom field of the common closure of every p-adic field:
`ε(A ⊗ ω_s, ψ, μ) = ε(A, ψ, μ) · q_F^(-(a(A) + n(ψ) dim A) s)` for every supplied
local-constant system, genuine continuous representation `A`, finite-inertia
presentation with surjectivity, and `s ∈ ℂ`.

The Library reduction `SpectralConductor.spectralConductorRankOneReduction` derives the
formula from two propositions, refinement invariance of presentation conductors and
rank-one conductor transport at intermediate fields. Both are proved in the Library,
by `Ramification.Padic.finiteInertiaConductorRefinement` and
`SpectralConductor.commonClosureRankOneConductor`.
-/

universe uF uV

namespace Langlands.LocalFactor.ConductorExponent

/-- Tate (3.4.5) and Deligne (5.5.2) for every prime `p` and every p-adic field `F`, at
independent field and representation-carrier universes. -/
theorem spectralConductor :
    ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p),
      SpectralConductorStatement.{uF, uV} F := by
  intro p _ F
  exact SpectralConductor.spectralConductorRankOneReduction.{uF, uV} F
    (fun A => Ramification.Padic.finiteInertiaConductorRefinement F A)
    (SpectralConductor.commonClosureRankOneConductor p F)

end Langlands.LocalFactor.ConductorExponent
