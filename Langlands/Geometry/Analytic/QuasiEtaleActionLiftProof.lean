import Langlands.Geometry.Analytic.QuasiEtaleActionLiftStatement
import Langlands.Geometry.Analytic.ActionLiftFromAutomorphismLifts
import Langlands.Geometry.Analytic.KeyLemma.QuasiEtaleAutomorphismLift

/-! # Lifts of continuous actions to compact quasi-étale spaces -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Reduction of the action-lift statement** to the lifting of near-identity automorphisms:
uniqueness comes from the rigidity of quasi-étale morphisms with compact source, existence from
`QuasiEtaleAutomorphismLiftStatement`. -/
theorem quasiEtaleActionLift_of_automorphismLift
    (hlift : QuasiEtaleAutomorphismLiftStatement.{u, v} K) :
    QuasiEtaleActionLiftStatement.{u, v, z} K := by
  intro G _ _ _ X U ρ f hX hρ hf hU
  have hrig : IsRigid f := isRigid_of_quasiEtale f hf hU
  exact ⟨nonempty_actionLift_of_automorphismLift hρ hrig (hlift X U f hX hf hU),
    fun a b => ActionLift.exists_agreeOn hrig a b⟩

/-- **Lifts of continuous actions to compact quasi-étale spaces.** A continuous action of a
topological group on a Hausdorff analytic space `X` lifts, on an open subgroup, to every compact
space `U` quasi-étale over `X`, and any two lifts agree on an open subgroup. -/
theorem quasiEtaleActionLift : QuasiEtaleActionLiftStatement.{u, v, z} K :=
  quasiEtaleActionLift_of_automorphismLift quasiEtaleAutomorphismLift

end Langlands.Analytic.SaturatedAtlasPresentation
