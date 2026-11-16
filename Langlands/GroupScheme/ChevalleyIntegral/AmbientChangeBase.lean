import Langlands.GroupScheme.ChevalleyIntegral.ParameterChangeBase
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Ambient matrix cell points under a change of base -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n]
  {R S : CommRingCat.{u}} (a : Spec S ⟶ Spec R)

/-- Regard an old-base matrix point on a new-base test scheme as a new-base point. -/
def extendPoint (T : Over (Spec S)) (x : (Over.map a).obj T ⟶ (groupScheme n R).X) :
    T ⟶ (groupScheme n S).X :=
  (pointsEquiv n S T).symm (pointsEquiv n R ((Over.map a).obj T) x)

@[simp] theorem pointsEquiv_extendPoint (T : Over (Spec S))
    (x : (Over.map a).obj T ⟶ (groupScheme n R).X) :
    pointsEquiv n S T (extendPoint n a T x) =
      pointsEquiv n R ((Over.map a).obj T) x :=
  (pointsEquiv n S T).apply_symm_apply _

private theorem exists_blockUnipotentExtend (e : n → ℤ) (T : Over (Spec S))
    (x : (Over.map a).obj T ⟶ (blockUnipotentScheme n R e).X) :
    ∃ y : T ⟶ (blockUnipotentScheme n S e).X,
      y ≫ (blockUnipotentHom n S e).hom.hom =
        extendPoint n a T (x ≫ (blockUnipotentHom n R e).hom.hom) := by
  apply SubgroupFunctor.mem_range.mp
  rw [(isRepresentedBy_blockUnipotent n S e).2]
  change pointsEquiv n S T _ ∈ blockUnipotentSubgroup Γ(T.left, ⊤) e
  rw [pointsEquiv_extendPoint]
  exact ((isRepresentedBy_blockUnipotent n R e).pointsEquiv _ x).property

/-- Lift a block-unipotent point to the new base, keeping its actual matrix. -/
def blockUnipotentExtend (e : n → ℤ) (T : Over (Spec S))
    (x : (Over.map a).obj T ⟶ (blockUnipotentScheme n R e).X) :
    T ⟶ (blockUnipotentScheme n S e).X :=
  (exists_blockUnipotentExtend n a e T x).choose

@[simp] theorem blockUnipotentExtend_points (e : n → ℤ) (T : Over (Spec S))
    (x : (Over.map a).obj T ⟶ (blockUnipotentScheme n R e).X) :
    pointsEquiv n S T (blockUnipotentExtend n a e T x ≫
        (blockUnipotentHom n S e).hom.hom) =
      pointsEquiv n R ((Over.map a).obj T) (x ≫ (blockUnipotentHom n R e).hom.hom) := by
  rw [blockUnipotentExtend, (exists_blockUnipotentExtend n a e T x).choose_spec,
    pointsEquiv_extendPoint]

private theorem exists_blockLeviExtend (e : n → ℤ) (T : Over (Spec S))
    (x : (Over.map a).obj T ⟶ (blockLeviScheme n R e).X) :
    ∃ y : T ⟶ (blockLeviScheme n S e).X,
      y ≫ (blockLeviHom n S e).hom.hom =
        extendPoint n a T (x ≫ (blockLeviHom n R e).hom.hom) := by
  apply SubgroupFunctor.mem_range.mp
  rw [(isRepresentedBy_blockLevi n S e).2]
  change pointsEquiv n S T _ ∈ blockLeviSubgroup Γ(T.left, ⊤) e
  rw [pointsEquiv_extendPoint]
  exact ((isRepresentedBy_blockLevi n R e).pointsEquiv _ x).property

/-- Lift a block-Levi point to the new base, keeping its actual matrix. -/
def blockLeviExtend (e : n → ℤ) (T : Over (Spec S))
    (x : (Over.map a).obj T ⟶ (blockLeviScheme n R e).X) :
    T ⟶ (blockLeviScheme n S e).X :=
  (exists_blockLeviExtend n a e T x).choose

@[simp] theorem blockLeviExtend_points (e : n → ℤ) (T : Over (Spec S))
    (x : (Over.map a).obj T ⟶ (blockLeviScheme n R e).X) :
    pointsEquiv n S T (blockLeviExtend n a e T x ≫
        (blockLeviHom n S e).hom.hom) =
      pointsEquiv n R ((Over.map a).obj T) (x ≫ (blockLeviHom n R e).hom.hom) := by
  rw [blockLeviExtend, (exists_blockLeviExtend n a e T x).choose_spec,
    pointsEquiv_extendPoint]

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  {R S : CommRingCat.{u}} (a : Spec S ⟶ Spec R)

/-- Lift all three ambient block factors to the new base on the same test scheme. -/
def ambientCellExtend (T : Over (Spec S)) (x : (Over.map a).obj T ⟶ D.ambientCellSpace R) :
    T ⟶ D.ambientCellSpace S :=
  lift (GeneralLinear.blockUnipotentExtend (Fin D.n) a D.neg.ellWeights T (x ≫ fst _ _))
    (lift (GeneralLinear.blockLeviExtend (Fin D.n) a D.ellWeights T (x ≫ snd _ _ ≫ fst _ _))
      (GeneralLinear.blockUnipotentExtend (Fin D.n) a D.ellWeights T
        (x ≫ snd _ _ ≫ snd _ _)))

/-- The lifted ambient point has exactly the original matrix triple product. -/
@[simp] theorem ambientCellExtend_comp (T : Over (Spec S))
    (x : (Over.map a).obj T ⟶ D.ambientCellSpace R) :
    D.matrixRestrict a T (D.ambientCellExtend a T x ≫ D.ambientCellMap S) =
      x ≫ D.ambientCellMap R := by
  apply (GeneralLinear.pointsEquiv (Fin D.n) R _).injective
  rw [pointsEquiv_matrixRestrict]
  simp only [ambientCellMap, Dynamic.tripleCellMultiplication,
    SubgroupFunctor.cellMultiplication, ambientCellExtend, MonObj.comp_mul,
    lift_fst_assoc, lift_snd_assoc, Category.assoc, GeneralLinear.pointsEquiv_mul,
    GeneralLinear.blockUnipotentExtend_points, GeneralLinear.blockLeviExtend_points]

end Langlands.GroupScheme.SplitExistence.ChevalleyData
