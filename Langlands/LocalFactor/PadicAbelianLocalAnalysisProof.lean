import Langlands.LocalFactor.Abelian.ZetaEulerTest
import Langlands.LocalFactor.Abelian.TateFunctionalEquation

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.LocalFactor

universe u

/-- Tate local analysis for every supplied p-adic field realization. -/
theorem padicAbelianLocalAnalysis : PadicAbelianLocalAnalysisStatement.{u} := by
  classical
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  dsimp only
  refine ⟨⟨PadicAbelian.uniformizerUnit T, PadicAbelian.uniformizerUnit_ord T⟩, ?_, ?_, ?_⟩
  · intro χ
    exact ⟨PadicAbelian.quasicharacter_open_kernel T χ,
      PadicAbelian.quasicharacter_locallyConstant T χ,
      PadicAbelian.quasicharacter_norm_units T χ,
      PadicAbelian.quasicharacter_finite_unit_image T χ,
      PadicAbelian.existsUnique_conductorAt T χ⟩
  · intro χ η a b hχ hη
    refine ⟨PadicAbelian.conductorAt_inv T χ a hχ,
      PadicAbelian.conductorAt_mul_le T χ η a b hχ hη,
      PadicAbelian.conductorAt_mul_of_ne T χ η a b hχ hη, ?_⟩
    intro hb
    subst hb
    exact PadicAbelian.conductorAt_mul_unramified T χ η a hχ hη
  · intro π hπ χ a hχ μ
    refine ⟨PadicAbelian.haar_integer_units_masses T μ,
      ⟨PadicAbelian.lFactorAt_meromorphicNFOn T π χ a,
        PadicAbelian.lFactorAt_ne_zero_of_regular T π χ a⟩,
      PadicAbelian.zeta_analysis T π hπ χ a hχ μ,
      PadicAbelian.test_function_euler T π hπ χ a hχ μ, ?_⟩
    intro ψ n hψ
    refine ⟨?_, PadicAbelian.epsilonAt_differentiable T π χ ψ.toAddChar μ.measure a n,
      PadicAbelian.epsilonAt_eq_zero_mul T π χ ψ.toAddChar μ.measure a n,
      PadicAbelian.epsilonAt_eq_half_mul T π χ ψ.toAddChar μ.measure a n,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s
      exact ⟨PadicAbelian.gaussIntegrand_integrable T χ ψ μ (n + a) s,
        PadicAbelian.epsilonAt_ne_zero T π χ hχ ψ n μ hψ s⟩
    · intro ρ hρ s
      exact ⟨PadicAbelian.lFactorAt_uniformizer_eq T χ hχ hπ hρ s,
        PadicAbelian.epsilonAt_uniformizer_eq T χ ψ.toAddChar μ.measure hχ n hπ hρ s⟩
    · exact PadicAbelian.epsilonAt_eq_shell T π hπ χ ψ.toAddChar μ.measure hχ n
    · intro r _ s
      exact PadicAbelian.epsilonAt_smul_measure T π χ ψ.toAddChar μ.measure a n r s
    · exact PadicAbelian.epsilonAt_mulShift T π hπ χ ψ.toAddChar μ hχ n
    · intro ω hω
      refine ⟨PadicAbelian.epsilonAt_mul_unramified T π hπ χ ω hω ψ.toAddChar μ.measure a n,
        ?_⟩
      intro t ht s
      exact ⟨PadicAbelian.lFactorAt_mul_unramified T π χ ω a t ht s,
        PadicAbelian.epsilonAt_mul_unramified_shift T π hπ χ ω hω ψ.toAddChar
          μ.measure a n t ht s⟩
    · intro ν hmass s
      exact PadicAbelian.epsilonAt_mul_epsilonAt_inv T π χ hχ ψ n μ ν.measure hψ
        inferInstance hmass s
    · exact PadicAbelian.norm_epsilonAt_half T π χ hχ ψ n μ hψ
    · intro f
      exact PadicAbelian.fourier_functional_equation T π hπ χ hχ ψ hψ μ f

end Langlands.LocalFactor
