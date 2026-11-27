import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GeneralLinearCartanCoveringStatement

/-! # Cartan coverings for any generic diagonal cocharacter of `GL_n` -/

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped ValuativeRel

namespace Langlands.HarishChandraSchwartz

open Aubert.General.RationalPointFamily (FiniteCartanCovering)

universe u

/-- The same standard integral subgroup gives the ambient and Levi Cartan
coverings for every generic diagonal cocharacter of the general linear group. -/
def GeneralLinearGenericCartanCoveringStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ),
    let i := GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)
    let K := (GroupScheme.GeneralLinear.standardIntegralModel ↥𝒪[F] F (Fin N)).integralPoints
    haveI := GroupScheme.GeneralLinear.isAffineHom_groupScheme
      (n := Fin N) (R := CommRingCat.of F)
    ∀ ν : cocharacterLattice
        (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))),
      IsGenericCocharacter i ν →
        FiniteCartanCovering F i ν K ∧
          ∀ J ⊆ simpleRelativeRoots i ν, StandardLeviCartanCovering F i ν J K

end Langlands.HarishChandraSchwartz
