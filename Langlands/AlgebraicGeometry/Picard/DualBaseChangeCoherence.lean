import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityProof
import Langlands.AbelianScheme.BaseChangeCoherence

/-! # Identity and composition of the actual canonical dual base-change comparison -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- At identity base change the total-space comparison is induced by the actual
identity comparison of the abelian scheme and the identity of the parameter. -/
lemma familyBaseChangeSpaceMap_id (T : Over S) :
    familyBaseChangeSpaceMap (𝟙 S) A T =
      (homFamilySpaceMap (baseChangeIdIso A).hom).app T ≫
        (relativeSpace A.X.hom).map ((Over.mapId S).inv.app T) := by
  apply pullback.hom_ext
  · simp [relativeSpace, Category.assoc, homFamilySpaceMap_fst]
    exact familyBaseChangeSpaceMap_fst (𝟙 S) A T
  · simp only [Category.assoc, relativeSpace, Functor.comp_map, Over.forget_map,
      Over.pullback_map_left, pullback.lift_snd, homFamilySpaceMap_snd]
    change familyBaseChangeSpaceMap (𝟙 S) A T ≫
        pullback.snd ((Over.map (𝟙 S)).obj T).hom A.X.hom =
      pullback.snd T.hom ((baseChange (𝟙 S)).obj A).X.hom ≫
        (GroupScheme.baseChangeIdIso A.toGrp).hom.hom.hom.left
    rw [GroupScheme.baseChangeIdIso_hom_left]
    exact familyBaseChangeSpaceMap_snd (𝟙 S) A T

/-- Identity ground-base pullback of actual rigidified families agrees with
pullback along the actual abelian-scheme identity comparison. -/
def familyBaseChangeIdIso (T : Over S) :
    familyBaseChange (𝟙 S) A T ≅
      RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          ((Over.mapId S).inv.app T) ⋙
        homFamilyPullback (baseChangeIdIso A).hom T := by
  refine RigidifiedLineBundle.pullbackCongr (familyBaseChangeSpaceMap_id A T)
    (show 𝟙 T.left = 𝟙 T.left ≫ ((Over.mapId S).inv.app T).left by simp)
    (by simp) (by
      rw [← Category.assoc, relativeSection_homFamilySpaceMap]
      simpa using ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality
        ((Over.mapId S).inv.app T)).symm) ≪≫ ?_
  exact (RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence
    ((relativeSpace A.X.hom).map ((Over.mapId S).inv.app T))
    ((Over.mapId S).inv.app T).left
    ((homFamilySpaceMap (baseChangeIdIso A).hom).app T) (𝟙 T.left) _ _
    (by
      rw [← Category.assoc, relativeSection_homFamilySpaceMap]
      simpa using ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality
        ((Over.mapId S).inv.app T)).symm)).symm

/-- Identity ground-base pullback on rigidified classes is the map of the
canonical abelian-scheme comparison, with the required parameter transport. -/
lemma rigidifiedClassesBaseChange_id (T : Over S)
    (q : RigidifiedClasses A ((Over.map (𝟙 S)).obj T)) :
    rigidifiedClassesBaseChange (𝟙 S) A T q =
      homClassesPullback (baseChangeIdIso A).hom T
        (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
          ((Over.mapId S).inv.app T) q) := by
  refine Quotient.inductionOn q (fun L => ?_)
  exact Quotient.sound ⟨(familyBaseChangeIdIso A T).app L⟩

/-- The parameter projection at identity pullback is the canonical identity comparison. -/
lemma baseChangeParameterMap_id (P : Over S) :
    (Over.mapId S).inv.app ((Over.pullback (𝟙 S)).obj P) ≫
        baseChangeParameterMap (𝟙 S) P =
      Over.pullbackId.hom.app P := by
  ext
  simp [baseChangeParameterMap, Over.pullbackId, conjugateIsoEquiv,
    conjugateEquiv, Over.mapPullbackAdj]

/-- The canonical dual base-change map at the identity is the dual of the actual
abelian-scheme identity comparison, after the parameter comparison. -/
lemma dualSchemeBaseChangeIso_id
    (stability : PicardZeroPullbackStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (hA : HasDualScheme A) (hA' : HasDualScheme ((baseChange (𝟙 S)).obj A)) :
    (dualSchemeBaseChangeIso universality (𝟙 S) A hA hA').hom =
      Over.pullbackId.hom.app (dualScheme A hA) ≫
        dualSchemeMap homPicardZeroPullback (baseChangeIdIso A).hom hA' hA := by
  apply dualPointClass_injective stability ((baseChange (𝟙 S)).obj A) hA'
  apply Subtype.ext
  have h := dualPointClass_dualSchemeBaseChangeIso (𝟙 S) A stability universality hA hA'
    (𝟙 ((Over.pullback (𝟙 S)).obj (dualScheme A hA)))
  rw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp,
    rigidifiedClassesBaseChange_id] at h
  rw [h, dualPointClass_dualSchemeMap]
  change homClassesPullback (baseChangeIdIso A).hom _
    (RigidifiedLineBundle.classesPullback _ _ _ _
      (RigidifiedLineBundle.classifyingMap _ _ _ _ _ _)) =
    homClassesPullback (baseChangeIdIso A).hom _
      (RigidifiedLineBundle.classifyingMap _ _ _ _ _ _)
  rw [← RigidifiedLineBundle.classifyingMap_comp _ _ _ RigidifiedModule.pullbackCoherence,
    baseChangeParameterMap_id]

section Composition

variable {S' S'' : Scheme.{u}} (b : S' ⟶ S) (c : S'' ⟶ S')

/-- Direct and successive ground-base maps of family total spaces agree after the
actual abelian-scheme and parameter comparisons. -/
lemma familyBaseChangeSpaceMap_comp (T : Over S'') :
    familyBaseChangeSpaceMap c ((baseChange b).obj A) T ≫
        familyBaseChangeSpaceMap b A ((Over.map c).obj T) =
      (homFamilySpaceMap (baseChangeCompIso b c A).inv).app T ≫
        familyBaseChangeSpaceMap (c ≫ b) A T ≫
          (relativeSpace A.X.hom).map ((Over.mapComp c b).hom.app T) := by
  apply pullback.hom_ext
  · simp [familyBaseChangeSpaceMap, homFamilySpaceMap, relativeSpace, Category.assoc]
  · simp [familyBaseChangeSpaceMap, homFamilySpaceMap, relativeSpace, Category.assoc]
    change _ = pullback.snd T.hom ((baseChange c).obj ((baseChange b).obj A)).X.hom ≫
      (GroupScheme.baseChangeCompIso b c A.toGrp).inv.hom.hom.left ≫
        pullback.fst A.X.hom (c ≫ b)
    rw [GroupScheme.baseChangeCompIso_inv_fst]
    rfl

/-- Successive ground-base pullback of actual rigidified families is the direct
pullback transported by the canonical abelian-scheme and parameter comparisons. -/
def familyBaseChangeCompIso (T : Over S'') :
    familyBaseChange b A ((Over.map c).obj T) ⋙
        familyBaseChange c ((baseChange b).obj A) T ≅
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          ((Over.mapComp c b).hom.app T) ⋙ familyBaseChange (c ≫ b) A T) ⋙
        homFamilyPullback (baseChangeCompIso b c A).inv T := by
  let hparam := (Over.mapComp c b).hom.app T
  let iRight₁ := RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence
    (ε := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
      ((Over.map b).obj ((Over.map c).obj T)))
    (ε' := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
      ((Over.map (c ≫ b)).obj T))
    (ε'' := (relativeSection ((baseChange (c ≫ b)).obj A).X.hom
      (unitSection ((baseChange (c ≫ b)).obj A)) (unitSection_comp _)).app T)
    ((relativeSpace A.X.hom).map hparam) hparam.left
    (familyBaseChangeSpaceMap (c ≫ b) A T) (𝟙 T.left)
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality hparam).symm
    (by simp)
    (by rw [← Category.assoc, relativeSection_familyBaseChangeSpaceMap]
        simpa using ((relativeSection A.X.hom (unitSection A)
          (unitSection_comp A)).naturality hparam).symm)
  let iRight₂ := RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence
    (ε := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
      ((Over.map b).obj ((Over.map c).obj T)))
    (ε' := (relativeSection ((baseChange (c ≫ b)).obj A).X.hom
      (unitSection ((baseChange (c ≫ b)).obj A)) (unitSection_comp _)).app T)
    (ε'' := (relativeSection ((baseChange c).obj ((baseChange b).obj A)).X.hom
      (unitSection ((baseChange c).obj ((baseChange b).obj A))) (unitSection_comp _)).app T)
    (familyBaseChangeSpaceMap (c ≫ b) A T ≫ (relativeSpace A.X.hom).map hparam)
    (𝟙 T.left ≫ hparam.left)
    ((homFamilySpaceMap (baseChangeCompIso b c A).inv).app T) (𝟙 T.left)
    (by rw [← Category.assoc, relativeSection_familyBaseChangeSpaceMap]
        simpa using ((relativeSection A.X.hom (unitSection A)
          (unitSection_comp A)).naturality hparam).symm)
    (by simp)
    (by rw [← Category.assoc, relativeSection_homFamilySpaceMap,
          ← Category.assoc, relativeSection_familyBaseChangeSpaceMap]
        simpa using ((relativeSection A.X.hom (unitSection A)
          (unitSection_comp A)).naturality hparam).symm)
  refine RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence
    (familyBaseChangeSpaceMap b A ((Over.map c).obj T)) (𝟙 T.left)
    (familyBaseChangeSpaceMap c ((baseChange b).obj A) T) (𝟙 T.left) _ _
    (by rw [← Category.assoc, relativeSection_familyBaseChangeSpaceMap]; simp) ≪≫ ?_
  exact RigidifiedLineBundle.pullbackCongr (familyBaseChangeSpaceMap_comp A b c T)
      (by simp [hparam]) _ _ ≪≫ iRight₂.symm ≪≫
    (Functor.isoWhiskerRight iRight₁
      (homFamilyPullback (baseChangeCompIso b c A).inv T)).symm

/-- Direct and successive ground-base pullback agree on actual rigidified
classes after both canonical comparison maps. -/
lemma rigidifiedClassesBaseChange_comp (T : Over S'')
    (q : RigidifiedClasses A ((Over.map b).obj ((Over.map c).obj T))) :
    rigidifiedClassesBaseChange c ((baseChange b).obj A) T
        (rigidifiedClassesBaseChange b A ((Over.map c).obj T) q) =
      homClassesPullback (baseChangeCompIso b c A).inv T
        (rigidifiedClassesBaseChange (c ≫ b) A T
          (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
            ((Over.mapComp c b).hom.app T) q)) := by
  refine Quotient.inductionOn q (fun L => ?_)
  exact Quotient.sound ⟨(familyBaseChangeCompIso A b c T).app L⟩

/-- The iterated parameter mate is the direct mate after the canonical slice
comparison. This is an equation of actual morphisms of parameter schemes. -/
lemma baseChangeParameterMate_comp {P : Over S} {T : Over S''}
    (p : T ⟶ (Over.pullback c).obj ((Over.pullback b).obj P)) :
    (Over.mapComp c b).hom.app T ≫
        baseChangeParameterMate b (baseChangeParameterMate c p) =
      baseChangeParameterMate (c ≫ b) (p ≫ (Over.pullbackComp c b).inv.app P) := by
  ext
  simp [baseChangeParameterMate, baseChangeParameterMap, Over.pullbackComp,
    conjugateIsoEquiv, Adjunction.comp_counit_app, Category.assoc]

/-- The parameter projection of successive pullback is the direct projection
composed with the canonical comparison. -/
lemma baseChangeParameterMap_comp (P : Over S) :
    (Over.mapComp c b).hom.app ((Over.pullback c).obj ((Over.pullback b).obj P)) ≫
        (Over.map b).map (baseChangeParameterMap c ((Over.pullback b).obj P)) ≫
          baseChangeParameterMap b P =
      baseChangeParameterMate (c ≫ b) ((Over.pullbackComp c b).inv.app P) := by
  simpa [baseChangeParameterMate] using
    baseChangeParameterMate_comp b c (𝟙 ((Over.pullback c).obj ((Over.pullback b).obj P)))

/-- Successive canonical dual-scheme base change equals direct base change,
with the actual parameter and abelian-scheme comparison maps. -/
lemma dualSchemeBaseChangeIso_comp_inv
    (stability : PicardZeroPullbackStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (hA : HasDualScheme A) (hAb : HasDualScheme ((baseChange b).obj A))
    (hAd : HasDualScheme ((baseChange (c ≫ b)).obj A))
    (hAc : HasDualScheme ((baseChange c).obj ((baseChange b).obj A))) :
    (Over.pullback c).map (dualSchemeBaseChangeIso universality b A hA hAb).hom ≫
        (dualSchemeBaseChangeIso universality c ((baseChange b).obj A) hAb hAc).hom =
      (Over.pullbackComp c b).inv.app (dualScheme A hA) ≫
        (dualSchemeBaseChangeIso universality (c ≫ b) A hA hAd).hom ≫
          dualSchemeMap homPicardZeroPullback (baseChangeCompIso b c A).inv hAc hAd := by
  apply dualPointClass_injective stability ((baseChange c).obj ((baseChange b).obj A)) hAc
  apply Subtype.ext
  rw [dualPointClass_dualSchemeBaseChangeIso c ((baseChange b).obj A)
      stability universality hAb hAc,
    baseChangeParameterMap_naturality,
    dualPointClass_dualSchemeBaseChangeIso b A stability universality hA hAb,
    rigidifiedClassesBaseChange_comp,
    ← Category.assoc, dualPointClass_dualSchemeMap]
  change homClassesPullback _ _ _ = homClassesPullback _ _
    ((dualPointClass stability ((baseChange (c ≫ b)).obj A) hAd
      ((Over.pullbackComp c b).inv.app (dualScheme A hA) ≫
        (dualSchemeBaseChangeIso universality (c ≫ b) A hA hAd).hom)).val)
  rw [dualPointClass_dualSchemeBaseChangeIso (c ≫ b) A stability universality hA hAd]
  change homClassesPullback _ _
      (rigidifiedClassesBaseChange _ _ _
        (RigidifiedLineBundle.classesPullback _ _ _ _
          (RigidifiedLineBundle.classifyingMap _ _ _ _ _ _))) =
    homClassesPullback _ _
      (rigidifiedClassesBaseChange _ _ _
        (RigidifiedLineBundle.classifyingMap _ _ _ _ _ _))
  rw [← RigidifiedLineBundle.classifyingMap_comp _ _ _ RigidifiedModule.pullbackCoherence]
  rw [baseChangeParameterMap_comp]
  rfl

/-- The forward direct-to-successive parameter comparison commutes with the
canonical dual base-change maps. -/
lemma dualSchemeBaseChangeIso_comp
    (stability : PicardZeroPullbackStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (hA : HasDualScheme A) (hAb : HasDualScheme ((baseChange b).obj A))
    (hAd : HasDualScheme ((baseChange (c ≫ b)).obj A))
    (hAc : HasDualScheme ((baseChange c).obj ((baseChange b).obj A))) :
    (Over.pullbackComp c b).hom.app (dualScheme A hA) ≫
        (Over.pullback c).map (dualSchemeBaseChangeIso universality b A hA hAb).hom ≫
          (dualSchemeBaseChangeIso universality c ((baseChange b).obj A) hAb hAc).hom =
      (dualSchemeBaseChangeIso universality (c ≫ b) A hA hAd).hom ≫
        dualSchemeMap homPicardZeroPullback (baseChangeCompIso b c A).inv hAc hAd := by
  rw [dualSchemeBaseChangeIso_comp_inv A b c stability universality hA hAb hAd hAc]
  simp

end Composition

end Langlands.AbelianScheme


