import Langlands.GroupScheme.IntegralModel.LocalField
import Langlands.GroupScheme.IntegralModel.GeneralLinearLattice
import Langlands.GroupScheme.Rational.GeneralLinearIndexing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm

/-! # The actual Cartan covering for the general linear group and its standard Levis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz

open Aubert.General.RationalPointFamily (FiniteCartanCovering)

/-- The Cartan coverings for the diagonal torus of `GL_N` and each standard Levi,
with the integral points of the standard model as their common ambient compact. -/
def GeneralLinearCartanCoveringStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ),
    let i := GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    let K := (GroupScheme.GeneralLinear.standardIntegralModel ↥𝒪[F] F (Fin N)).integralPoints
    haveI := GroupScheme.GeneralLinear.isAffineHom_groupScheme
      (n := Fin N) (R := CommRingCat.of F)
    ∀ ν : cocharacterLattice
        (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))),
      StrictAnti (GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin N) F ν) →
        FiniteCartanCovering F i ν K ∧
          ∀ J ⊆ simpleRelativeRoots i ν, StandardLeviCartanCovering F i ν J K

end Langlands.HarishChandraSchwartz
