import Langlands.Representation.Conductor.SphericalCorankOneLaurentStatement
import Langlands.Representation.Conductor.SphericalLFactorGenerationReduction
import Langlands.Representation.Conductor.SphericalCorankOneConvergenceProof
import Langlands.Representation.Conductor.UnramifiedCorankOneLaurentFromMultiplicativity
import Langlands.Representation.Conductor.OrderedUnramifiedWhittakerProof
import Langlands.Representation.RankinSelberg.LocalFieldPrincipalSeriesLFactorMultiplicativityProof
import Langlands.Representation.RankinSelberg.LocalFieldPrincipalSeriesGammaMultiplicativityProof

/-!
# Proof of the convergence and Laurent clauses for the spherical functions

`UnramifiedCorankOneLaurentStatement` holds over every nonarchimedean local field: the
bridge `unramifiedCorankOneLaurent_of_multiplicativity` applies to the proved L- and
gamma-factor multiplicativity theorems for unramified principal series (JPSS 1983,
Theorem (3.1)). With the proved convergence statement and Jacquet's Lemma 2
(`orderedUnramifiedWhittakerRealization`), this gives `SphericalCorankOneLaurentStatement`,
the first three conjuncts of `SphericalLFactorGenerationStatement`.
-/

namespace Langlands.Conductor

open Langlands.RankinSelberg Polynomial

universe uF uV

/-- JPSS 1983, Theorem (3.1)(ii), for the corank-one integrals of `π × I(x)`, over every
nonarchimedean local field. -/
theorem unramifiedCorankOneLaurent : UnramifiedCorankOneLaurentStatement.{uF, uV} :=
  unramifiedCorankOneLaurent_of_multiplicativity localFieldPrincipalSeriesLFactorMultiplicativity
    localFieldPrincipalSeriesGammaMultiplicativity

/-- The standard L-polynomial of `π`, convergence of the corank-one integrals against
`W(x; ψ̄)` and their Laurent numerators, for every Satake parameter `x`, over every
nonarchimedean local field. -/
theorem sphericalCorankOneLaurent : SphericalCorankOneLaurentStatement.{uF, uV} := by
  intro F _ _ _ _ n _ _ _ _ _ _ _ _ q ψ abv ϖ μ h V _ _ π hπ ℓ hℓ
  obtain ⟨P, hP, hc⟩ := sphericalCorankOneConvergence F n q ψ abv ϖ μ h π hπ ℓ hℓ
  refine ⟨P, hP, hc, fun w x => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_perm_monotone_norm x
  obtain ⟨a, N, Q, hQ⟩ := laurent_of_ordered h hπ hℓ hP unramifiedCorankOneLaurent
    orderedUnramifiedWhittakerRealization (x ∘ σ) hσ w (by
      rw [inverseSphericalWhittaker_comp_perm h.conductor.1 h.uniformizer q x σ]
      exact hc w x)
  refine ⟨a, N, Q, fun s hs => ?_⟩
  rw [← inverseSphericalWhittaker_comp_perm h.conductor.1 h.uniformizer q x σ,
    ← prod_comp_perm P x σ]
  exact hQ s hs

end Langlands.Conductor
