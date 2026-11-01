import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityStatement
import Langlands.AlgebraicGeometry.Picard.DualBaseChangeClasses

/-! # Naturality of the canonical dual base-change comparison -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules

section Family

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {A B : AbelianScheme S}

/-- The base change of a homomorphism lies over the original homomorphism. -/
@[reassoc]
lemma hom_baseChange_map_fst (f : A ⟶ B) :
    hom ((baseChange b).map f) ≫ pullback.fst B.X.hom b =
      pullback.fst A.X.hom b ≫ hom f := by
  change ((Over.pullback b).map (groupHom f).hom.hom).left ≫ _ = _
  simp

/-- The total-space comparison for ground base change commutes with the total-space maps
of a homomorphism and of its base change. -/
lemma familyBaseChangeSpaceMap_baseChangeHom (f : A ⟶ B) (T : Over S') :
    familyBaseChangeSpaceMap b A T ≫ (homFamilySpaceMap f).app ((Over.map b).obj T) =
      (homFamilySpaceMap ((baseChange b).map f)).app T ≫ familyBaseChangeSpaceMap b B T := by
  apply pullback.hom_ext
  · simp only [Category.assoc, familyBaseChangeSpaceMap_fst, homFamilySpaceMap_fst]
  · simp only [Category.assoc, familyBaseChangeSpaceMap_snd, homFamilySpaceMap_snd,
      homFamilySpaceMap_snd_assoc, familyBaseChangeSpaceMap_snd_assoc,
      hom_baseChange_map_fst]

/-- Ground base change of rigidified families commutes with pullback along a homomorphism
and along its base change. -/
def familyBaseChangeHomPullbackIso (f : A ⟶ B) (T : Over S') :
    homFamilyPullback f ((Over.map b).obj T) ⋙ familyBaseChange b A T ≅
      familyBaseChange b B T ⋙ homFamilyPullback ((baseChange b).map f) T :=
  RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence
    ((homFamilySpaceMap f).app ((Over.map b).obj T)) (𝟙 T.left)
    (familyBaseChangeSpaceMap b A T) (𝟙 T.left) _ _
    (by rw [← Category.assoc, relativeSection_familyBaseChangeSpaceMap]
        simp) ≪≫
  RigidifiedLineBundle.pullbackCongr (familyBaseChangeSpaceMap_baseChangeHom b f T) rfl _ _ ≪≫
  (RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence
    (familyBaseChangeSpaceMap b B T) (𝟙 T.left)
    ((homFamilySpaceMap ((baseChange b).map f)).app T) (𝟙 T.left) _ _
    (by rw [← Category.assoc, relativeSection_homFamilySpaceMap]
        simp)).symm

/-- On rigidified classes, ground base change commutes with homomorphism pullback. -/
lemma rigidifiedClassesBaseChange_homClassesPullback (f : A ⟶ B) (T : Over S')
    (q : RigidifiedClasses B ((Over.map b).obj T)) :
    rigidifiedClassesBaseChange b A T (homClassesPullback f ((Over.map b).obj T) q) =
      homClassesPullback ((baseChange b).map f) T (rigidifiedClassesBaseChange b B T q) := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact Quotient.sound ⟨(familyBaseChangeHomPullbackIso b f T).app L⟩

/-- The projection from a base-changed parameter scheme is natural in the parameter scheme. -/
@[reassoc]
lemma baseChangeParameterMap_naturality {P Q : Over S} (g : P ⟶ Q) :
    (Over.map b).map ((Over.pullback b).map g) ≫ baseChangeParameterMap b Q =
      baseChangeParameterMap b P ≫ g := by
  ext
  simp [baseChangeParameterMap]

end Family

section Dual

variable (stability : PicardZeroPullbackStatement.{u})
variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable {S S' : Scheme.{u}} (b : S' ⟶ S) {A B : AbelianScheme S}

include stability in
/-- The canonical base-change comparisons of the chosen duals are natural with respect to the
classified dual scheme maps. -/
lemma dualSchemeMap_dualSchemeBaseChangeIso (f : A ⟶ B)
    (hA : HasDualScheme A) (hB : HasDualScheme B)
    (hA' : HasDualScheme ((baseChange b).obj A)) (hB' : HasDualScheme ((baseChange b).obj B)) :
    (Over.pullback b).map (dualSchemeMap homPicardZeroPullback f hA hB) ≫
        (dualSchemeBaseChangeIso universality b A hA hA').hom =
      (dualSchemeBaseChangeIso universality b B hB hB').hom ≫
        dualSchemeMap homPicardZeroPullback ((baseChange b).map f) hA' hB' := by
  apply dualPointClass_injective stability ((baseChange b).obj A) hA'
  apply Subtype.ext
  rw [dualPointClass_dualSchemeBaseChangeIso b A stability universality hA hA',
    baseChangeParameterMap_naturality, dualPointClass_dualSchemeMap,
    dualPointClass_dualSchemeMap]
  have h := dualPointClass_dualSchemeBaseChangeIso b B stability universality hB hB'
    (𝟙 ((Over.pullback b).obj (dualScheme B hB)))
  rw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact (rigidifiedClassesBaseChange_homClassesPullback b f _ _).trans
    (congrArg (homClassesPullback ((baseChange b).map f) _) h.symm)

end Dual

/-- The canonical dual base-change comparison commutes with the dual of every actual
abelian-scheme homomorphism. -/
theorem dualAbelianBaseChangeNaturality : DualAbelianBaseChangeNaturalityStatement.{u} := by
  intro preservation stability composition unitCoherence associativity comparison symmetry
    universality compatibility S S' b A B hA geometryA MA evaluationA hB geometryB MB evaluationB
    hA' geometryA' MA' evaluationA' hB' geometryB' MB' evaluationB' f
  apply Additive.toMul.injective
  apply Grp.hom_ext
  change (Over.pullback b).map (dualSchemeMap homPicardZeroPullback f hA hB) ≫
      (groupHom (dualAbelianBaseChangeIso preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility b A
        hA geometryA MA evaluationA hA' geometryA' MA' evaluationA').hom).hom.hom =
    (groupHom (dualAbelianBaseChangeIso preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility b B
        hB geometryB MB evaluationB hB' geometryB' MB' evaluationB').hom).hom.hom ≫
      dualSchemeMap homPicardZeroPullback ((baseChange b).map f) hA' hB'
  rw [dualAbelianBaseChangeIso_hom, dualAbelianBaseChangeIso_hom]
  exact dualSchemeMap_dualSchemeBaseChangeIso stability universality b f hA hB hA' hB'

end Langlands.AbelianScheme
