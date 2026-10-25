import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeStatement
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeNaturality

/-! # Group compatibility of the canonical dual base-change comparison -/

universe u
open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

private def familyClassesBaseChange (T : Over S') :
    RigidifiedClasses A ((Over.map b).obj T) → RigidifiedClasses ((baseChange b).obj A) T :=
  Quotient.map (familyBaseChange b A T).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(familyBaseChange b A T).mapIso e⟩)

private lemma familyClassesBaseChange_naturality {T U : Over S'} (h : T ⟶ U)
    (q : RigidifiedClasses A ((Over.map b).obj U)) :
    RigidifiedLineBundle.classesPullback ((baseChange b).obj A).X.hom
        (unitSection ((baseChange b).obj A)) (unitSection_comp _) h
        (familyClassesBaseChange b A U q) =
      familyClassesBaseChange b A T
        (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
          ((Over.map b).map h) q) := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact Quotient.sound ⟨(familyBaseChangeNaturality b A h).symm.app L⟩

private lemma familyClassesBaseChange_tensor
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorLeftUnitorStatement.{u})
    (T : Over S') (q r : RigidifiedClasses A ((Over.map b).obj T)) :
    familyClassesBaseChange b A T
        (RigidifiedLineBundle.classesTensor preservation A.X.hom (unitSection A)
          (unitSection_comp A) ((Over.map b).obj T) q r) =
      RigidifiedLineBundle.classesTensor preservation ((baseChange b).obj A).X.hom
        (unitSection ((baseChange b).obj A)) (unitSection_comp _) T
        (familyClassesBaseChange b A T q) (familyClassesBaseChange b A T r) := by
  refine Quotient.inductionOn₂ q r (fun L M ↦ ?_)
  exact Quotient.sound ⟨RigidifiedLineBundle.pullbackTensorIso preservation composition
    unitCoherence (familyBaseChangeSpaceMap b A T) (𝟙 T.left) (by simp) L M⟩

private lemma baseChangeFamily_classifyingMap (P : Over S) (L : RigidifiedFamily A P)
    {T : Over S'} (p : T ⟶ (Over.pullback b).obj P) :
    RigidifiedLineBundle.classifyingMap ((baseChange b).obj A).X.hom
        (unitSection ((baseChange b).obj A)) (unitSection_comp _)
        ((baseChangeFamily b A P).obj L) T p =
      familyClassesBaseChange b A T
        (RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
          L ((Over.map b).obj T) ((Over.map b).map p ≫ baseChangeParameterMap b P)) := by
  change RigidifiedLineBundle.classesPullback _ _ _ p
    (familyClassesBaseChange b A _
      (RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
        L _ (baseChangeParameterMap b P))) = _
  rw [familyClassesBaseChange_naturality,
    RigidifiedLineBundle.classifyingMap_comp _ _ _ RigidifiedModule.pullbackCoherence]

private lemma dualBaseChange_point_class
    (stability : PicardZeroPullbackStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (hA : HasDualScheme A) (hA' : HasDualScheme ((baseChange b).obj A))
    {T : Over S'} (p : T ⟶ (Over.pullback b).obj (dualScheme A hA)) :
    (dualPointClass stability ((baseChange b).obj A) hA'
      (p ≫ (dualSchemeBaseChangeIso universality b A hA hA').hom)).val =
      familyClassesBaseChange b A T
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
  exact baseChangeFamily_classifyingMap b A (dualScheme A hA) (poincareFamily A hA) p

private def isoOfPointMultiplication {B C : AbelianScheme S}
    (e : B.X ≅ C.X)
    (hmul : ∀ (T : Over S) (p q : T ⟶ B.X),
      (p * q) ≫ e.hom = (p ≫ e.hom) * (q ≫ e.hom)) : B ≅ C := by
  let φ (T : Over S) : (T ⟶ B.X) ≃* (T ⟶ C.X) :=
    { toFun := fun p ↦ p ≫ e.hom
      invFun := fun q ↦ q ≫ e.inv
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp
      map_mul' := hmul T }
  have hone : η[B.X] ≫ e.hom = η[C.X] := by
    have h := (φ (MonoidalCategory.tensorUnit (Over S))).map_one
    change (1 : MonoidalCategory.tensorUnit (Over S) ⟶ B.X) ≫ e.hom =
      (1 : MonoidalCategory.tensorUnit (Over S) ⟶ C.X) at h
    simpa only [CategoryTheory.Hom.one_def,
      CartesianMonoidalCategory.toUnit_unique
        (CartesianMonoidalCategory.toUnit (MonoidalCategory.tensorUnit (Over S))) (𝟙 _),
      Category.id_comp] using h
  have hprod : μ[B.X] ≫ e.hom =
      MonoidalCategory.tensorHom e.hom e.hom ≫ μ[C.X] := by
    have h := hmul (MonoidalCategory.tensorObj B.X B.X)
      (CartesianMonoidalCategory.fst B.X B.X) (CartesianMonoidalCategory.snd B.X B.X)
    simpa only [CategoryTheory.Hom.mul_def, CartesianMonoidalCategory.lift_fst_snd,
      Category.id_comp, CartesianMonoidalCategory.lift_fst_comp_snd_comp] using h
  let g : B.toGrp ≅ C.toGrp := Grp.mkIso e hone hprod
  exact
    { hom := Additive.ofMul g.hom
      inv := Additive.ofMul g.inv
      hom_inv_id := congrArg Additive.ofMul g.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul g.inv_hom_id }

/-- The prescribed Poincare-compatible comparison is an isomorphism of the
actual constructed dual abelian schemes, for every inverse/evaluation choice. -/
theorem dualAbelianBaseChange : DualAbelianBaseChangeStatement.{u} := by
  intro preservation stability composition unitCoherence associativity comparison symmetry
    universality S S' b A hA geometryA MA evaluationA hA' geometryA' MA' evaluationA'
  let D := dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
    stability composition unitCoherence associativity comparison symmetry
  let D' := dualAbelianSchemeFromEvaluation ((baseChange b).obj A) hA' geometryA'
    preservation MA' evaluationA' stability composition unitCoherence associativity comparison symmetry
  let e : ((baseChange b).obj D).X ≅ D'.X :=
    dualSchemeBaseChangeIso universality b A hA hA'
  have hmul (T : Over S') (p q : T ⟶ ((baseChange b).obj D).X) :
      (p * q) ≫ e.hom = (p ≫ e.hom) * (q ≫ e.hom) := by
    let := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry A ((Over.map b).obj T)
    let := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry ((baseChange b).obj A) T
    let := RigidifiedLineBundle.classesCommMonoid preservation unitCoherence associativity
      comparison symmetry A.X.hom (unitSection A) (unitSection_comp A) ((Over.map b).obj T)
    let := RigidifiedLineBundle.classesCommMonoid preservation unitCoherence associativity
      comparison symmetry ((baseChange b).obj A).X.hom (unitSection ((baseChange b).obj A))
      (unitSection_comp _) T
    let F : (T ⟶ ((baseChange b).obj D).X) →* RigidifiedClasses A ((Over.map b).obj T) :=
      (picardZeroInclusionMonoidHom preservation unitCoherence associativity comparison symmetry
        A ((Over.map b).obj T)).comp
        ((dualAbelianSchemePointMulEquiv A hA geometryA preservation MA evaluationA stability
          composition unitCoherence associativity comparison symmetry ((Over.map b).obj T)).toMonoidHom.comp
          (GroupScheme.baseChangePointsEquiv b D.toGrp T).toMonoidHom)
    let G : (T ⟶ D'.X) →* RigidifiedClasses ((baseChange b).obj A) T :=
      (picardZeroInclusionMonoidHom preservation unitCoherence associativity comparison symmetry
        ((baseChange b).obj A) T).comp
        (dualAbelianSchemePointMulEquiv ((baseChange b).obj A) hA' geometryA' preservation
          MA' evaluationA' stability composition unitCoherence associativity comparison symmetry T).toMonoidHom
    have hG : Function.Injective G :=
      Subtype.val_injective.comp (dualAbelianSchemePointMulEquiv ((baseChange b).obj A) hA'
        geometryA' preservation MA' evaluationA' stability composition unitCoherence associativity
        comparison symmetry T).injective
    have hc (x : T ⟶ ((baseChange b).obj D).X) :
        G (x ≫ e.hom) = familyClassesBaseChange b A T (F x) :=
      dualBaseChange_point_class b A stability universality hA hA' x
    apply hG
    rw [map_mul, hc, hc, hc, map_mul]
    exact familyClassesBaseChange_tensor b A preservation composition unitCoherence.1 T (F p) (F q)
  exact ⟨isoOfPointMultiplication e hmul, rfl⟩

end Langlands.AbelianScheme
