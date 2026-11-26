import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Reductive.RootDatum

/-! # Renard's simultaneous compact-open basis for the integral points of `GL_N` -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

/-- The standard integral points of `GL_N` satisfy the simultaneous standard basis
property for the diagonal torus and each generic cocharacter. -/
def GeneralLinearSimultaneousStandardBasisStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N)))),
    let i := GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    IsGenericCocharacter i ν →
      SimultaneousStandardBasisAt i ν
        (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints

end Langlands.BruhatTits.SpecialCompact
