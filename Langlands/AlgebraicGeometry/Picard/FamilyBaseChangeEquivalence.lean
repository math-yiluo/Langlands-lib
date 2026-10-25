import Langlands.AlgebraicGeometry.Picard.PoincareBaseChange
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

/-! # Equivalence of actual rigidified families across ground base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

/-- The inverse to the canonical map between the two actual relative spaces. -/
def familyBaseChangeSpaceInv (T : Over S') :
    (relativeSpace A.X.hom).obj ((Over.map b).obj T) ⟶
      (relativeSpace ((baseChange b).obj A).X.hom).obj T :=
  pullback.lift (pullback.fst (T.hom ≫ b) A.X.hom)
    (pullback.lift (pullback.snd (T.hom ≫ b) A.X.hom)
      (pullback.fst (T.hom ≫ b) A.X.hom ≫ T.hom)
      (by rw [Category.assoc]; exact pullback.condition.symm))
    (by exact (pullback.lift_snd _ _ _).symm)

/-- Changing the ground base does not change the family over a fixed S'-scheme. -/
def familyBaseChangeSpaceIso (T : Over S') :
    (relativeSpace ((baseChange b).obj A).X.hom).obj T ≅
      (relativeSpace A.X.hom).obj ((Over.map b).obj T) where
  hom := familyBaseChangeSpaceMap b A T
  inv := familyBaseChangeSpaceInv b A T
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [familyBaseChangeSpaceInv, Category.assoc, pullback.lift_fst,
        Category.id_comp]
      exact familyBaseChangeSpaceMap_fst b A T
    · apply pullback.hom_ext
      · simp only [familyBaseChangeSpaceInv, Category.assoc, pullback.lift_snd_assoc,
          pullback.lift_fst, Category.id_comp]
        exact familyBaseChangeSpaceMap_snd b A T
      · simp only [familyBaseChangeSpaceInv, Category.assoc, pullback.lift_snd,
          Category.id_comp]
        change familyBaseChangeSpaceMap b A T ≫
          pullback.fst ((Over.map b).obj T).hom A.X.hom ≫ T.hom = _
        rw [familyBaseChangeSpaceMap_fst_assoc]
        exact pullback.condition
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, familyBaseChangeSpaceMap_fst]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, familyBaseChangeSpaceMap_snd, ← Category.assoc]
      dsimp only [familyBaseChangeSpaceInv]
      erw [pullback.lift_snd, pullback.lift_fst]
      exact (Category.id_comp _).symm

@[simp]
lemma relativeSection_familyBaseChangeSpaceInv (T : Over S') :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
        ((Over.map b).obj T) ≫ familyBaseChangeSpaceInv b A T =
      (relativeSection ((baseChange b).obj A).X.hom
        (unitSection ((baseChange b).obj A)) (unitSection_comp _)).app T := by
  rw [← relativeSection_familyBaseChangeSpaceMap b A T, Category.assoc]
  change _ ≫ (familyBaseChangeSpaceIso b A T).hom ≫
    (familyBaseChangeSpaceIso b A T).inv = _
  simp

/-- Pull back along the inverse comparison, keeping the specified rigidification. -/
def familyBaseChangeInverse (T : Over S') :
    RigidifiedFamily ((baseChange b).obj A) T ⥤
      RigidifiedFamily A ((Over.map b).obj T) :=
  RigidifiedLineBundle.pullback (familyBaseChangeSpaceInv b A T) (𝟙 T.left)
    (by simp)

/-- The two successive rigidified pullbacks recover the original family. -/
def familyBaseChangeUnitIso (T : Over S') :
    familyBaseChange b A T ⋙ familyBaseChangeInverse b A T ≅
      𝟭 (RigidifiedFamily A ((Over.map b).obj T)) :=
  RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence
    (familyBaseChangeSpaceMap b A T) (𝟙 T.left)
    (familyBaseChangeSpaceInv b A T) (𝟙 T.left) _ _
    (by simp [← Category.assoc]) ≪≫
  RigidifiedLineBundle.pullbackCongr (familyBaseChangeSpaceIso b A T).inv_hom_id
    (Category.id_comp _) _ _ ≪≫
  RigidifiedLineBundle.pullbackId RigidifiedModule.pullbackCoherence _

/-- The inverse pullback followed by ground-base pullback recovers the new family. -/
def familyBaseChangeCounitIso (T : Over S') :
    familyBaseChangeInverse b A T ⋙ familyBaseChange b A T ≅
      𝟭 (RigidifiedFamily ((baseChange b).obj A) T) :=
  RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence
    (familyBaseChangeSpaceInv b A T) (𝟙 T.left)
    (familyBaseChangeSpaceMap b A T) (𝟙 T.left) _ _
    (by simp [← Category.assoc]) ≪≫
  RigidifiedLineBundle.pullbackCongr (familyBaseChangeSpaceIso b A T).hom_inv_id
    (Category.id_comp _) _ _ ≪≫
  RigidifiedLineBundle.pullbackId RigidifiedModule.pullbackCoherence _

/-- The existing actual ground-base pullback is an equivalence of rigidified families. -/
def familyBaseChangeEquivalence (T : Over S') :
    RigidifiedFamily A ((Over.map b).obj T) ≌
      RigidifiedFamily ((baseChange b).obj A) T :=
  CategoryTheory.Equivalence.mk (familyBaseChange b A T) (familyBaseChangeInverse b A T)
    (familyBaseChangeUnitIso b A T).symm (familyBaseChangeCounitIso b A T)

end Langlands.AbelianScheme
