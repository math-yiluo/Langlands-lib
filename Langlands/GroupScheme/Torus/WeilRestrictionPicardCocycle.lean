import Langlands.GroupScheme.Torus.WeilRestrictionAffineEvaluation
import Langlands.GroupScheme.Torus.PicardTrivialCocycle

/-! # Weil-restriction cocycles over Picard-trivial coefficient rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

open WeilGm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B : CommRingCat.{u}} [Algebra A B]
  [Module.Finite A B] [Module.Projective A B] {U : Over (Spec A)}
  (ξ : Cocycle (WeilGm.groupScheme A B) U)

/-- Pull back to the coefficient base and evaluate the cocycle as units. -/
def coefficientUnitCocycle :
    Cocycle (splitTorus (Spec B) PUnit) (coefficientTest A B U) where
  toFun {Z} a b := (splitTorus.pointsEquiv PUnit Z).symm fun _ =>
    evaluationUnits A B Z
      (ξ.toFun ((Over.map (baseMap A B)).map a ≫ coefficientProjection A B U)
        ((Over.map (baseMap A B)).map b ≫ coefficientProjection A B U))
  naturality t a b := by
    apply (splitTorus.pointsEquiv PUnit _).injective
    simp only [MulEquiv.apply_symm_apply, splitTorus.pointsEquiv_naturality]
    funext i
    change evaluationUnits A B _ (ξ.toFun _ _) =
      Units.map t.left.appTop.hom.toMonoidHom (evaluationUnits A B _ (ξ.toFun _ _))
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      ξ.naturality, evaluationUnits_naturality]
  cocycle a b c := by
    apply (splitTorus.pointsEquiv PUnit _).injective
    simp only [MulEquiv.apply_symm_apply, map_mul]
    funext i
    change evaluationUnits A B _ (ξ.toFun _ _) = _ * _
    rw [ξ.cocycle _ ((Over.map (baseMap A B)).map b ≫ coefficientProjection A B U) _,
      map_mul]

local instance coefficientCover_isAffineHom [IsAffineHom U.hom] :
    IsAffineHom (coefficientTest A B U).hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom U.hom›

local instance coefficientCover_flat [Flat U.hom] :
    Flat (coefficientTest A B U).hom := by
  change Flat (pullback.snd U.hom (baseMap A B))
  infer_instance

local instance coefficientCover_surjective [Surjective U.hom] :
    Surjective (coefficientTest A B U).hom := by
  change Surjective (pullback.snd U.hom (baseMap A B))
  infer_instance

local instance cover_isAffine [IsAffineHom U.hom] : IsAffine U.left :=
  isAffine_of_isAffineHom U.hom

variable [Subsingleton (CommRing.Pic B)] [IsAffineHom U.hom]
  [Flat U.hom] [Surjective U.hom]

/-- A global unit on the coefficient-base cover cobounding the evaluated cocycle. -/
def coefficientPicardUnit : Γ((coefficientTest A B U).left, ⊤)ˣ :=
  splitTorus.pointsEquiv PUnit (coefficientTest A B U)
    ξ.coefficientUnitCocycle.splitPicardCochain PUnit.unit

theorem coefficientPicardUnit_spec {Z : Over (Spec B)}
    (a b : Z ⟶ coefficientTest A B U) :
    evaluationUnits A B Z
        (ξ.toFun ((Over.map (baseMap A B)).map a ≫ coefficientProjection A B U)
          ((Over.map (baseMap A B)).map b ≫ coefficientProjection A B U)) =
      Units.map a.left.appTop.hom.toMonoidHom ξ.coefficientPicardUnit *
        (Units.map b.left.appTop.hom.toMonoidHom ξ.coefficientPicardUnit)⁻¹ := by
  have h := ξ.coefficientUnitCocycle.splitPicardCochain_spec a b
  have hc := congrArg (fun x => splitTorus.pointsEquiv PUnit Z x PUnit.unit) h
  simpa only [coefficientUnitCocycle, MulEquiv.apply_symm_apply, map_mul, map_inv,
    Pi.mul_apply, Pi.inv_apply, splitTorus.pointsEquiv_naturality,
    splitTorus.unitsRestrict, MonoidHom.compLeft_apply, Function.comp_apply,
    coefficientPicardUnit] using hc

/-- Recover the unit coboundary as a Weil-restriction point on the original cover. -/
def weilPicardCochain : U ⟶ (WeilGm.groupScheme A B).X :=
  (affineEvaluationEquiv A B U).symm ξ.coefficientPicardUnit

theorem weilPicardCochain_evaluation :
    coefficientEvaluation A B U ξ.weilPicardCochain = ξ.coefficientPicardUnit := by
  rw [← affineEvaluationEquiv_apply]
  exact (affineEvaluationEquiv A B U).apply_symm_apply _

theorem weilPicardCochain_spec_affine {Z : Over (Spec A)} [IsAffine Z.left]
    (a b : Z ⟶ U) :
    ξ.toFun a b = (a ≫ ξ.weilPicardCochain) * (b ≫ ξ.weilPicardCochain)⁻¹ := by
  apply (affineEvaluationEquiv A B Z).injective
  rw [map_mul, map_inv, affineEvaluationEquiv_naturality,
    affineEvaluationEquiv_naturality, affineEvaluationEquiv_apply,
    affineEvaluationEquiv_apply, weilPicardCochain_evaluation]
  have h := ξ.coefficientPicardUnit_spec ((Over.pullback (baseMap A B)).map a)
    ((Over.pullback (baseMap A B)).map b)
  rw [coefficientProjection_naturality, coefficientProjection_naturality,
    ξ.naturality] at h
  exact h

/-- The recovered point cobounds the Weil-restriction cocycle on every test. -/
theorem weilPicardCochain_spec {Z : Over (Spec A)} (a b : Z ⟶ U) :
    ξ.toFun a b = (a ≫ ξ.weilPicardCochain) * (b ≫ ξ.weilPicardCochain)⁻¹ := by
  let P : Over (Spec A) := Over.mk (pullback.fst U.hom U.hom ≫ U.hom)
  let p₁ : P ⟶ U := Over.homMk (pullback.fst U.hom U.hom) rfl
  let p₂ : P ⟶ U := Over.homMk (pullback.snd U.hom U.hom) pullback.condition.symm
  let t : Z ⟶ P := Over.homMk
    (pullback.lift a.left b.left ((Over.w a).trans (Over.w b).symm)) (by
      change pullback.lift a.left b.left _ ≫
        (pullback.fst U.hom U.hom ≫ U.hom) = Z.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact Over.w a)
  have ht₁ : t ≫ p₁ = a := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have ht₂ : t ≫ p₂ = b := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  have : IsAffine P.left := by
    change IsAffine (pullback U.hom U.hom)
    infer_instance
  have h := ξ.weilPicardCochain_spec_affine p₁ p₂
  have ht := congrArg (fun x => t ≫ x) h
  simpa only [← ξ.naturality, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, ht₁, ht₂] using ht

/-- Picard triviality of the coefficient ring kills WeilGm cocycles on affine
faithfully flat covers of the base. -/
theorem isTrivial_weil_of_pic_trivial : ξ.IsTrivial :=
  ⟨ξ.weilPicardCochain, ξ.weilPicardCochain_spec⟩

end Langlands.GroupScheme.Cocycle
