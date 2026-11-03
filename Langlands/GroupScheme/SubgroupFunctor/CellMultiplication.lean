import Langlands.GroupScheme.SubgroupFunctor

/-! # Multiplication from two subgroup sources -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G U P : GroupScheme S} (iU : U ⟶ G) (iP : P ⟶ G)

/-- Multiplication from two actual subgroup sources. -/
def cellMultiplication : U.X ⊗ P.X ⟶ G.X :=
  (fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)

@[simp]
theorem lift_cellMultiplication {T : Over S} (a : T ⟶ U.X) (b : T ⟶ P.X) :
    lift a b ≫ cellMultiplication iU iP =
      (a ≫ iU.hom.hom) * (b ≫ iP.hom.hom) := by
  simp only [cellMultiplication, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]

end Langlands.GroupScheme.SubgroupFunctor
