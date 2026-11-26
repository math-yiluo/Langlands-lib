import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Reductive.RootDatum

/-! # Integral Weyl representatives and standard parabolic factorization for `GL_N` -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

/-- The standard integral subgroup contains representatives of the relative Weyl
group and factors along each of the actual standard parabolics. -/
def GeneralLinearIntegralParabolicsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N)))),
    let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    let K := (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints
    IsGenericCocharacter i ν →
      HasWeylRepresentatives i K ∧ HasParabolicFactorization i ν K

end Langlands.BruhatTits.SpecialCompact
