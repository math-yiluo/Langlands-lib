import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeStatement
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeNaturality

/-! # Rigidified classes under dual base change -/

universe u
open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

def rigidifiedClassesBaseChange (T : Over S') :
    RigidifiedClasses A ((Over.map b).obj T) → RigidifiedClasses ((baseChange b).obj A) T :=
  Quotient.map (familyBaseChange b A T).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(familyBaseChange b A T).mapIso e⟩)

lemma rigidifiedClassesBaseChange_naturality {T U : Over S'} (h : T ⟶ U)
    (q : RigidifiedClasses A ((Over.map b).obj U)) :
    RigidifiedLineBundle.classesPullback ((baseChange b).obj A).X.hom
        (unitSection ((baseChange b).obj A)) (unitSection_comp _) h
        (rigidifiedClassesBaseChange b A U q) =
      rigidifiedClassesBaseChange b A T
        (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
          ((Over.map b).map h) q) := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact Quotient.sound ⟨(familyBaseChangeNaturality b A h).symm.app L⟩

lemma rigidifiedClassesBaseChange_tensor
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorLeftUnitorStatement.{u})
    (T : Over S') (q r : RigidifiedClasses A ((Over.map b).obj T)) :
    rigidifiedClassesBaseChange b A T
        (RigidifiedLineBundle.classesTensor preservation A.X.hom (unitSection A)
          (unitSection_comp A) ((Over.map b).obj T) q r) =
      RigidifiedLineBundle.classesTensor preservation ((baseChange b).obj A).X.hom
        (unitSection ((baseChange b).obj A)) (unitSection_comp _) T
        (rigidifiedClassesBaseChange b A T q) (rigidifiedClassesBaseChange b A T r) := by
  refine Quotient.inductionOn₂ q r (fun L M ↦ ?_)
  exact Quotient.sound ⟨RigidifiedLineBundle.pullbackTensorIso preservation composition
    unitCoherence (familyBaseChangeSpaceMap b A T) (𝟙 T.left) (by simp) L M⟩

lemma classifyingMap_baseChangeFamily (P : Over S) (L : RigidifiedFamily A P)
    {T : Over S'} (p : T ⟶ (Over.pullback b).obj P) :
    RigidifiedLineBundle.classifyingMap ((baseChange b).obj A).X.hom
        (unitSection ((baseChange b).obj A)) (unitSection_comp _)
        ((baseChangeFamily b A P).obj L) T p =
      rigidifiedClassesBaseChange b A T
        (RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
          L ((Over.map b).obj T) ((Over.map b).map p ≫ baseChangeParameterMap b P)) := by
  change RigidifiedLineBundle.classesPullback _ _ _ p
    (rigidifiedClassesBaseChange b A _
      (RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
        L _ (baseChangeParameterMap b P))) = _
  rw [rigidifiedClassesBaseChange_naturality,
    RigidifiedLineBundle.classifyingMap_comp _ _ _ RigidifiedModule.pullbackCoherence]

lemma dualPointClass_dualSchemeBaseChangeIso
    (stability : PicardZeroPullbackStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (hA : HasDualScheme A) (hA' : HasDualScheme ((baseChange b).obj A))
    {T : Over S'} (p : T ⟶ (Over.pullback b).obj (dualScheme A hA)) :
    (dualPointClass stability ((baseChange b).obj A) hA'
      (p ≫ (dualSchemeBaseChangeIso universality b A hA hA').hom)).val =
      rigidifiedClassesBaseChange b A T
        (dualPointClass stability A hA
          ((Over.map b).map p ≫ baseChangeParameterMap b (dualScheme A hA))).val := by
  change RigidifiedLineBundle.classifyingMap _ _ _ _ _ (p ≫ _) = _
  rw [RigidifiedLineBundle.classifyingMap_comp _ _ _ RigidifiedModule.pullbackCoherence]
  have h : RigidifiedLineBundle.classifyingMap ((baseChange b).obj A).X.hom
      (unitSection ((baseChange b).obj A)) (unitSection_comp _)
      (poincareFamily ((baseChange b).obj A) hA') _
      (dualSchemeBaseChangeIso universality b A hA hA').hom =
    RigidifiedLineBundle.classOf ((baseChange b).obj A).X.hom
      (unitSection ((baseChange b).obj A)) (unitSection_comp _)
      (poincareFamilyBaseChange b A hA) :=
    Quotient.sound ⟨dualSchemeBaseChangePullbackIso universality b A hA hA'⟩
  rw [h]
  exact classifyingMap_baseChangeFamily b A (dualScheme A hA) (poincareFamily A hA) p

end Langlands.AbelianScheme
