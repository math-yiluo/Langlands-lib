import Langlands.GroupScheme.Torus.FreeCharacterCover
import Langlands.GroupScheme.Torus.RelativeDiagonalizableHomLocality
import Langlands.GroupScheme.Torus.EndomorphismDichotomy
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Torus.Relative

/-! # Diagonalizable groups with free character group, and the free cover embedding -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

/-- A diagonalizable group with finite free character group is a split torus. -/
theorem isSplitTorus_diagonalizable (X : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ] : IsSplitTorus (diagonalizable X Λ) := by
  classical
  let b : Λ ≃+ (Module.Free.ChooseBasisIndex ℤ Λ → ℤ) :=
    (Module.Free.chooseBasis ℤ Λ).equivFun.toAddEquiv
  exact (Diagonalizable.isSplitTorus (CommRingCat.of (ULift.{u} ℤ)) b).baseChange _

/-- The diagonalizable group of the free cover of a finitely generated `Λ` is a split torus. -/
theorem isSplitTorus_diagonalizable_cover (X : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ]
    [AddGroup.FG Λ] : IsSplitTorus (diagonalizable X (FreeCharacterCover.Cover Λ)) :=
  isSplitTorus_diagonalizable X _

/-- `D_X(Λ) ⟶ D_X(F(Λ))`, induced by the projection `F(Λ) → Λ`, is a closed subgroup. -/
theorem isClosedSubgroup_diagonalizableMap_proj (X : Scheme.{u}) (Λ : Type u)
    [AddCommGroup Λ] :
    IsClosedSubgroup (diagonalizableMap X (FreeCharacterCover.proj Λ)) :=
  isClosedSubgroup_diagonalizableMap X _ (FreeCharacterCover.proj_surjective Λ)

end Langlands.GroupScheme.RelativeMultiplicativeType
