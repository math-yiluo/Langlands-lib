import Langlands.GroupScheme.IntegralModel.LocalField
import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Rational.GeneralLinearIndexing
import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty

/-! # A simultaneous standard-parabolic basis at the general linear integral compact -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

/-- The standard general linear integral model supplies the simultaneous
Renard basis at its integral-point subgroup for every generic cocharacter
of the diagonal torus. -/
def GeneralLinearSimultaneousBasisStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ),
    let i := GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    let K := (GroupScheme.GeneralLinear.standardIntegralModel ↥𝒪[F] F (Fin N)).integralPoints
    haveI := GroupScheme.GeneralLinear.isAffineHom_groupScheme
      (n := Fin N) (R := CommRingCat.of F)
    ∀ ν : cocharacterLattice
        (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))),
      IsGenericCocharacter i ν → SimultaneousStandardBasisAt i ν K

end Langlands.HarishChandraSchwartz
