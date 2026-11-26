import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GeneralLinearSimultaneousBasisStatement
import Langlands.BruhatTits.SpecialCompact.CongruenceBasis.Assembly
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Reductive.GeneralLinearIsConnectedReductiveProof

/-! # Simultaneous standard basis from the standard general linear integral model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

open GroupScheme.GeneralLinear

/-- All diagonal cocharacters lift to the same integral model, whose congruence
tower gives the published simultaneous standard basis. -/
theorem generalLinearSimultaneousBasis : GeneralLinearSimultaneousBasisStatement.{u} := by
  intro F _ _ _ _ N
  dsimp only
  intro ν hν
  let M := standardIntegralModel ↥𝒪[F] F (Fin N)
  have hG := GroupScheme.GeneralLinear.isConnectedReductiveStatement F (Fin N)
  have hi := isMaximalSplitTorus_diagonalTorus (n := Fin N) F
  apply CongruenceGL.simultaneousStandardBasisAt_integralPoints M hG hi hν
  intro y
  let w := cocharacterCoordEquiv (Fin N) F y
  refine ⟨diagonalCocharacter (Fin N) (CommRingCat.of ↥𝒪[F]) w, ?_⟩
  have wy : cocharacterOfWeights F w = y :=
    (cocharacterCoordEquiv (Fin N) F).symm_apply_apply y
  rw [← wy, cocharacterOfWeights_comp_diagonalTorus]
  exact baseChangeCocharacter_diagonalCocharacter (Spec.algebraMap ↥𝒪[F] F) w

end Langlands.HarishChandraSchwartz
