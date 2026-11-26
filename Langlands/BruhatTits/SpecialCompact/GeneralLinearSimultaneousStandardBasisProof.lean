import Langlands.BruhatTits.SpecialCompact.GeneralLinearSimultaneousStandardBasisStatement
import Langlands.BruhatTits.SpecialCompact.CongruenceBasis.Assembly
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Rational.GeneralLinearIndexing

/-! # Proof of the simultaneous compact-open basis for `GL_N` -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

/-- The standard integral model lifts every diagonal cocharacter, so its
congruence tower supplies the simultaneous basis. -/
theorem generalLinearSimultaneousStandardBasis :
    GeneralLinearSimultaneousStandardBasisStatement.{u} := by
  intro F _ _ _ _ N ν
  dsimp only
  intro hν
  refine CongruenceGL.simultaneousStandardBasisAt_integralPoints
    (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N))
    (isConnectedReductive_generalLinear F (Fin N))
    (GeneralLinear.isMaximalSplitTorus_diagonalTorus F) hν ?_
  intro y
  let w := GeneralLinear.cocharacterCoordEquiv (Fin N) F y
  refine ⟨GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of ↥𝒪[F]) w, ?_⟩
  dsimp only [IntegralModel.genericCocharacter, GeneralLinear.standardIntegralModel]
  rw [GeneralLinear.baseChangeCocharacter_diagonalCocharacter]
  simpa only [w, GeneralLinear.cocharacterOfWeights, LinearEquiv.symm_apply_apply] using
    (GeneralLinear.cocharacterOfWeights_comp_diagonalTorus F w).symm

end Langlands.BruhatTits.SpecialCompact
