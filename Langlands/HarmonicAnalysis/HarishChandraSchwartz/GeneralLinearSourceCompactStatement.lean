import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.Representation.Plancherel.WaldspurgerSourceNormalization

/-! # The geometric source compact of the general linear group -/

noncomputable section

universe u

open AlgebraicGeometry
open scoped ValuativeRel
open Langlands.GroupScheme Langlands.Plancherel.WaldspurgerSourceNormalization

namespace Langlands.HarishChandraSchwartz

/-- The standard integral-point compact of `GL_N` is the norm-one fixer of
a special vertex in the apartment of the actual diagonal split torus. -/
def GeneralLinearSourceCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ),
    haveI := GroupScheme.GeneralLinear.isAffineHom_groupScheme
      (n := Fin N) (R := CommRingCat.of F)
    IsSourceCompactAt
      (GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F))
      (GroupScheme.GeneralLinear.standardIntegralModel ↥𝒪[F] F (Fin N)).integralPoints

end Langlands.HarishChandraSchwartz
