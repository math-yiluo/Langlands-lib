import Langlands.GroupScheme.IntegralModel.LocalField
import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Rational.GeneralLinearIndexing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionSpecialCompact

/-! # Standard Iwasawa decompositions at the general linear integral compact -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

/-- The standard integral-point subgroup of `GL_N` has the Renard compact
properties and the actual minimal Iwasawa decompositions, including inside
every standard Levi. -/
def GeneralLinearIntegralCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ),
    let i := GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    let K := (GroupScheme.GeneralLinear.standardIntegralModel ↥𝒪[F] F (Fin N)).integralPoints
    haveI := GroupScheme.GeneralLinear.isAffineHom_groupScheme
      (n := Fin N) (R := CommRingCat.of F)
    ∀ ν : cocharacterLattice
        (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))),
      StrictAnti (GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin N) F ν) →
        SpecialCompactProperties F i ν K ∧
          IsIwasawaPair (standardParabolicPoints i ν ∅) K ∧
          StandardLeviIwasawaFactorsAt (i := i) (ν := ν) K

end Langlands.HarishChandraSchwartz
