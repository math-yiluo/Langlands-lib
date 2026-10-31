import Langlands.CategoryTheory.EquivariantDiagramCategory
import Langlands.CategoryTheory.EquivariantDiagramPreadditive
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Limits, colimits and abelian structure for varying-group equivariant diagrams -/

noncomputable section

universe uG uI vI uC vC uJ vJ

namespace Langlands.EquivariantDiagram

open CategoryTheory CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{uG}}
variable {C : Type uC} [Category.{vC} C]
variable {J : Type uJ} [Category.{vJ} J]

instance hasLimitsOfShape [HasLimitsOfShape J C] :
    HasLimitsOfShape J (EquivariantDiagram D C) :=
  Adjunction.hasLimitsOfShape_of_equivalence (indexEquivalence (D := D) (C := C)).functor

instance hasColimitsOfShape [HasColimitsOfShape J C] :
    HasColimitsOfShape J (EquivariantDiagram D C) :=
  Adjunction.hasColimitsOfShape_of_equivalence (indexEquivalence (D := D) (C := C)).functor

instance hasLimitsOfSize [HasLimitsOfSize.{vJ, uJ} C] :
    HasLimitsOfSize.{vJ, uJ} (EquivariantDiagram D C) where
  has_limits_of_shape _ _ := inferInstance

instance hasColimitsOfSize [HasColimitsOfSize.{vJ, uJ} C] :
    HasColimitsOfSize.{vJ, uJ} (EquivariantDiagram D C) where
  has_colimits_of_shape _ _ := inferInstance

instance hasFiniteLimits [HasFiniteLimits C] : HasFiniteLimits (EquivariantDiagram D C) where
  out _ _ _ := inferInstance

instance hasFiniteColimits [HasFiniteColimits C] : HasFiniteColimits (EquivariantDiagram D C) where
  out _ _ _ := inferInstance

/-- The existing pointwise preadditive structure makes varying-group diagrams abelian. -/
instance abelian [Abelian C] : Abelian (EquivariantDiagram D C) :=
  abelianOfEquivalence (indexEquivalence (D := D) (C := C)).functor

/-- Forgetting the actions is restriction of index functors along the base inclusion. -/
def forgetIndexIso : forget (D := D) (C := C) ≅
    toFunctor ⋙ (Functor.whiskeringLeft I (Index D) C).obj Index.inclusion :=
  NatIso.ofComponents (fun M => (forget (D := D) (C := C)).mapIso (fromToIso M)) (by
    intro M N c
    apply NatTrans.ext
    funext i
    change c.hom.app i ≫ 𝟙 _ = 𝟙 _ ≫ c.hom.app i
    simp)

instance forget_preservesLimitsOfShape [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (forget (D := D) (C := C)) := by
  have : PreservesLimitsOfShape J
      (toFunctor (D := D) (C := C) ⋙
        (Functor.whiskeringLeft I (Index D) C).obj Index.inclusion) := by
    change PreservesLimitsOfShape J
      ((indexEquivalence (D := D) (C := C)).functor ⋙ _)
    infer_instance
  exact preservesLimitsOfShape_of_natIso forgetIndexIso.symm

instance forget_preservesColimitsOfShape [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (forget (D := D) (C := C)) := by
  have : PreservesColimitsOfShape J
      (toFunctor (D := D) (C := C) ⋙
        (Functor.whiskeringLeft I (Index D) C).obj Index.inclusion) := by
    change PreservesColimitsOfShape J
      ((indexEquivalence (D := D) (C := C)).functor ⋙ _)
    infer_instance
  exact preservesColimitsOfShape_of_natIso forgetIndexIso.symm

instance evaluation_preservesLimitsOfShape (i : I) [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (evaluation (D := D) (C := C) i) := by
  apply Action.preservesLimitsOfShape_of_preserves
  change PreservesLimitsOfShape J
    (forget (D := D) (C := C) ⋙ (CategoryTheory.evaluation I C).obj i)
  infer_instance

instance evaluation_preservesColimitsOfShape (i : I) [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (evaluation (D := D) (C := C) i) := by
  apply Action.preservesColimitsOfShape_of_preserves
  change PreservesColimitsOfShape J
    (forget (D := D) (C := C) ⋙ (CategoryTheory.evaluation I C).obj i)
  infer_instance

instance forget_preservesFiniteLimits [HasFiniteLimits C] :
    PreservesFiniteLimits (forget (D := D) (C := C)) where
  preservesFiniteLimits _ _ _ := inferInstance

instance forget_preservesFiniteColimits [HasFiniteColimits C] :
    PreservesFiniteColimits (forget (D := D) (C := C)) where
  preservesFiniteColimits _ _ _ := inferInstance

instance evaluation_preservesFiniteLimits (i : I) [HasFiniteLimits C] :
    PreservesFiniteLimits (evaluation (D := D) (C := C) i) where
  preservesFiniteLimits _ _ _ := inferInstance

instance evaluation_preservesFiniteColimits (i : I) [HasFiniteColimits C] :
    PreservesFiniteColimits (evaluation (D := D) (C := C) i) where
  preservesFiniteColimits _ _ _ := inferInstance

end Langlands.EquivariantDiagram
