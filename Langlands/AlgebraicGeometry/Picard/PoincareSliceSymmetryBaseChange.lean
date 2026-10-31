import Langlands.AlgebraicGeometry.Picard.PoincareSliceSymmetry
import Langlands.AlgebraicGeometry.Picard.AmpleMumfordBaseChange
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeEquivalence
import Langlands.AlgebraicGeometry.Picard.TrivialPullbackTranslationInvariance

/-! # Slice symmetry of the Poincaré bundle descends along a change of base -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S) (hA : HasDualScheme A)

/-- The Poincaré line bundle of the changed abelian scheme is the pullback of the original one
along the inverse dual comparison followed by the actual total-space map. -/
def poincareBaseChangeForgetPullbackIso :
    (RigidifiedLineBundle.forget _).obj
        (poincareFamily ((baseChange b).obj A) (hasDualScheme_baseChange universality b A hA)) ≅
      (LineBundle.pullback ((relativeSpace ((baseChange b).obj A).X.hom).map
          (dualSchemeBaseChangeIso universality b A hA
            (hasDualScheme_baseChange universality b A hA)).inv ≫
          baseChangeFamilySpaceMap b A (dualScheme A hA))).obj
        ((RigidifiedLineBundle.forget _).obj (poincareFamily A hA)) :=
  let e := dualSchemeBaseChangeIso universality b A hA
    (hasDualScheme_baseChange universality b A hA)
  ((LineBundle.pullbackId _).app _).symm ≪≫
    LineBundle.pullbackEqIso (by rw [← CategoryTheory.Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]) _ ≪≫
    ((LineBundle.pullbackComp ((relativeSpace ((baseChange b).obj A).X.hom).map e.inv)
      ((relativeSpace ((baseChange b).obj A).X.hom).map e.hom)).app _).symm ≪≫
    (LineBundle.pullback ((relativeSpace ((baseChange b).obj A).X.hom).map e.inv)).mapIso
      ((RigidifiedLineBundle.forget _).mapIso
          (dualSchemeBaseChangePullbackIso universality b A hA
            (hasDualScheme_baseChange universality b A hA)) ≪≫
        poincareFamilyBaseChangeForgetIso b A hA) ≪≫
    (LineBundle.pullbackComp _ _).app _

/-- A map into the changed Poincaré space, followed by the inverse dual comparison and the
actual total-space map, is determined by its two projections to `D` and `A`. -/
lemma baseChangePoincareSpace_comp_eq {W : Scheme.{u}}
    (ψ' : W ⟶ (relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) (hasDualScheme_baseChange universality b A hA)))
    (ψ : W ⟶ (relativeSpace A.X.hom).obj (dualScheme A hA))
    (h₁ : ψ' ≫ pullback.fst _ _ ≫
        (dualSchemeBaseChangeIso universality b A hA
          (hasDualScheme_baseChange universality b A hA)).inv.left ≫
        pullback.fst (dualScheme A hA).hom b = ψ ≫ pullback.fst _ _)
    (h₂ : ψ' ≫ pullback.snd _ _ ≫ pullback.fst A.X.hom b = ψ ≫ pullback.snd _ _) :
    ψ' ≫ (relativeSpace ((baseChange b).obj A).X.hom).map
        (dualSchemeBaseChangeIso universality b A hA
          (hasDualScheme_baseChange universality b A hA)).inv ≫
        baseChangeFamilySpaceMap b A (dualScheme A hA) = ψ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, baseChangeFamilySpaceMap_fst]
    simp only [relativeSpace, Functor.comp_map, Over.forget_map, Over.pullback_map_left,
      pullback.lift_fst_assoc]
    exact h₁
  · rw [Category.assoc, Category.assoc, baseChangeFamilySpaceMap_snd]
    simp only [relativeSpace, Functor.comp_map, Over.forget_map, Over.pullback_map_left]
    erw [pullback.lift_snd_assoc]
    exact h₂

/-- Transport a pullback of the changed Poincaré line bundle to a pullback of the original
one along a map with matching projections. -/
def baseChangePoincarePullbackIso {W : Scheme.{u}}
    (ψ' : W ⟶ (relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) (hasDualScheme_baseChange universality b A hA)))
    (ψ : W ⟶ (relativeSpace A.X.hom).obj (dualScheme A hA))
    (h₁ : ψ' ≫ pullback.fst _ _ ≫
        (dualSchemeBaseChangeIso universality b A hA
          (hasDualScheme_baseChange universality b A hA)).inv.left ≫
        pullback.fst (dualScheme A hA).hom b = ψ ≫ pullback.fst _ _)
    (h₂ : ψ' ≫ pullback.snd _ _ ≫ pullback.fst A.X.hom b = ψ ≫ pullback.snd _ _) :
    (LineBundle.pullback ψ').obj ((RigidifiedLineBundle.forget _).obj
        (poincareFamily ((baseChange b).obj A) (hasDualScheme_baseChange universality b A hA))) ≅
      (LineBundle.pullback ψ).obj ((RigidifiedLineBundle.forget _).obj (poincareFamily A hA)) :=
  (LineBundle.pullback ψ').mapIso (poincareBaseChangeForgetPullbackIso universality b A hA) ≪≫
    LineBundle.pullbackCompEqIso ψ' _
      (baseChangePoincareSpace_comp_eq universality b A hA ψ' ψ h₁ h₂) _

/-- The changed map followed by the inverse dual comparison and the projection to `D` is the
projection to `A` followed by the original map. -/
@[reassoc]
lemma dualBaseChangeMap_left_inv_fst (f : A.X ⟶ dualScheme A hA) :
    (dualBaseChangeMap A hA universality b f).left ≫
        (dualSchemeBaseChangeIso universality b A hA
          (hasDualScheme_baseChange universality b A hA)).inv.left ≫
        pullback.fst (dualScheme A hA).hom b =
      (pullback.fst A.X.hom b : ((baseChange b).obj A).X.left ⟶ A.X.left) ≫ f.left := by
  have h := congrArg Over.Hom.left
    ((dualSchemeBaseChangeIso universality b A hA
      (hasDualScheme_baseChange universality b A hA)).hom_inv_id)
  rw [Over.comp_left, Over.id_left] at h
  erw [dualBaseChangeMap_eq, Over.comp_left, Category.assoc, reassoc_of% h]
  exact pullback.lift_fst _ _ _

/-- A point of the changed abelian scheme, read as a point of `A`. -/
@[reassoc]
lemma map_comp_baseChangeParameterMap_left {T' : Over S'} (t' : T' ⟶ ((baseChange b).obj A).X) :
    ((Over.map b).map t' ≫ baseChangeParameterMap b A.X).left =
      t'.left ≫ (pullback.fst A.X.hom b : ((baseChange b).obj A).X.left ⟶ A.X.left) :=
  rfl

/-- Slice symmetry of the Poincaré bundle descends along a change of base: if
`P'(f' t', a) ≅ P'(f' a, t')` on `T' ×_{S'} A'`, where `f'` is the changed map, then
`P(f t, a) ≅ P(f a, t)` on `T ×_S A` for the image point `t` of `t'`. -/
theorem poincareSliceSymmetric_of_baseChange (f : A.X ⟶ dualScheme A hA)
    {T' : Over S'} (t' : T' ⟶ ((baseChange b).obj A).X)
    (h : PoincareSliceSymmetric ((baseChange b).obj A)
      (hasDualScheme_baseChange universality b A hA)
      (dualBaseChangeMap A hA universality b f) t') :
    PoincareSliceSymmetric A hA f ((Over.map b).map t' ≫ baseChangeParameterMap b A.X) := by
  obtain ⟨i⟩ := h
  have : IsIso (familyBaseChangeSpaceMap b A T') :=
    (familyBaseChangeSpaceIso b A T').isIso_hom
  apply LineBundle.nonempty_iso_of_pullback_iso (familyBaseChangeSpaceMap b A T')
  refine LineBundle.pullbackCompEqIso _ _ rfl _ ≪≫
    (baseChangePoincarePullbackIso universality b A hA _ _ ?_ ?_).symm ≪≫ i ≪≫
    baseChangePoincarePullbackIso universality b A hA _ _ ?_ ?_ ≪≫
    (LineBundle.pullbackCompEqIso _ _ rfl _).symm
  all_goals simp only [Over.comp_left, Category.assoc, pairOver_left, pullback.lift_fst,
    pullback.lift_snd, relativeFst_left, relativeSnd_left, familyBaseChangeSpaceMap_fst_assoc,
    familyBaseChangeSpaceMap_snd_assoc, map_comp_baseChangeParameterMap_left]
  · erw [pullback.lift_fst_assoc]
    simp only [Category.assoc]
    rw [dualBaseChangeMap_left_inv_fst universality b A hA f]
    exact congrArg (pullback.fst T'.hom ((baseChange b).obj A).X.hom ≫ ·)
      (Category.assoc (Over.Hom.left t')
        (pullback.fst A.X.hom b : ((baseChange b).obj A).X.left ⟶ A.X.left) f.left).symm
  · erw [pullback.lift_snd_assoc]
    rw [familyBaseChangeSpaceMap_snd]
  · erw [pullback.lift_fst_assoc]
    simp only [Category.assoc]
    rw [dualBaseChangeMap_left_inv_fst universality b A hA f]
    exact rfl
  · erw [pullback.lift_snd_assoc]
    exact Category.assoc _ _ _

end Langlands.AbelianScheme
