import Langlands.GroupScheme.Torus.WeilRestrictionEvaluation
import Langlands.AlgebraicGeometry.AffineSchemeScalarExtension

/-! # Affine pullback evaluation of Weil-restriction points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.WeilGm

open Langlands.AlgebraicGeometry.SchemeFiberGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (A B : CommRingCat.{u}) [Algebra A B]

/-- The coefficient-ring base change of a test over `Spec A`. -/
abbrev coefficientTest (U : Over (Spec A)) : Over (Spec B) :=
  (Over.pullback (baseMap A B)).obj U

/-- Its projection to the original test, after restricting scalars. -/
def coefficientProjection (U : Over (Spec A)) :
    (Over.map (baseMap A B)).obj (coefficientTest A B U) ⟶ U :=
  Over.homMk (pullback.fst U.hom (baseMap A B)) pullback.condition

theorem coefficientProjection_naturality {U U' : Over (Spec A)} (a : U' ⟶ U) :
    (Over.map (baseMap A B)).map ((Over.pullback (baseMap A B)).map a) ≫
        coefficientProjection A B U =
      coefficientProjection A B U' ≫ a := by
  apply Over.OverMorphism.ext
  simp [coefficientProjection, Over.pullback_map_left]

/-- Actual global sections of an affine scalar extension in tensor coordinates. -/
def affinePullbackSectionsIso (U : Over (Spec A)) [IsAffine U.left] :
    CommRingCat.of (((algΓ A).obj U).unop ⊗[A] B) ≅
      Γ((coefficientTest A B U).left, ⊤) :=
  (Scheme.ΓSpecIso _).symm ≪≫
    Scheme.Γ.mapIso (affinePullbackTensorIso B U.hom).op

theorem affinePullbackSectionsIso_left (U : Over (Spec A)) [IsAffine U.left] :
    CommRingCat.ofHom (algebraMap (((algΓ A).obj U).unop)
        (((algΓ A).obj U).unop ⊗[A] B)) ≫
        (affinePullbackSectionsIso A B U).hom =
      (pullback.fst U.hom (baseMap A B)).appTop := by
  have h := congrArg Scheme.Hom.appTop (affinePullbackTensorIso_hom_fst B U.hom)
  simp only [Scheme.Hom.comp_appTop] at h
  dsimp only [affinePullbackSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Scheme.Γ_map]
  rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  calc
    _ = (Scheme.ΓSpecIso Γ(U.left, ⊤)).inv ≫
        U.left.isoSpec.hom.appTop ≫
        (pullback.fst U.hom (baseMap A B)).appTop :=
      congrArg (fun f => (Scheme.ΓSpecIso Γ(U.left, ⊤)).inv ≫ f) h
    _ = _ := by simp [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]

theorem affinePullbackSectionsIso_right (U : Over (Spec A)) [IsAffine U.left] :
    CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          B →ₐ[A] (((algΓ A).obj U).unop ⊗[A] B)).toRingHom ≫
        (affinePullbackSectionsIso A B U).hom =
      (Scheme.ΓSpecIso B).inv ≫ (pullback.snd U.hom (baseMap A B)).appTop := by
  have h := congrArg Scheme.Hom.appTop (affinePullbackTensorIso_hom_snd B U.hom)
  simp only [Scheme.Hom.comp_appTop] at h
  dsimp only [affinePullbackSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Scheme.Γ_map]
  rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  exact congrArg (fun f => (Scheme.ΓSpecIso B).inv ≫ f) h

/-- Tensor coordinates on the scalar extension, with the coefficient ring first. -/
def coefficientSectionsEquiv (U : Over (Spec A)) [IsAffine U.left] :
    B ⊗[A] ((algΓ A).obj U).unop ≃+* Γ((coefficientTest A B U).left, ⊤) :=
  (Algebra.TensorProduct.comm A B ((algΓ A).obj U).unop).toRingEquiv.trans
    (affinePullbackSectionsIso A B U).commRingCatIsoToRingEquiv

theorem coefficientSectionsEquiv_tmul (U : Over (Spec A)) [IsAffine U.left]
    (b : B) (r : ((algΓ A).obj U).unop) :
    coefficientSectionsEquiv A B U (b ⊗ₜ[A] r) =
      (((Scheme.ΓSpecIso B).inv ≫
        (pullback.snd U.hom (baseMap A B)).appTop) b) *
        (pullback.fst U.hom (baseMap A B)).appTop r := by
  change (affinePullbackSectionsIso A B U).hom (r ⊗ₜ[A] b) = _
  have hl := ConcreteCategory.congr_hom (affinePullbackSectionsIso_left A B U) r
  have hr := ConcreteCategory.congr_hom (affinePullbackSectionsIso_right A B U) b
  calc
    _ = (affinePullbackSectionsIso A B U).hom
          (algebraMap (((algΓ A).obj U).unop) (((algΓ A).obj U).unop ⊗[A] B) r) *
        (affinePullbackSectionsIso A B U).hom
          ((Algebra.TensorProduct.includeRight :
            B →ₐ[A] (((algΓ A).obj U).unop ⊗[A] B)) b) := by
      rw [← map_mul]
      congr 1
      simp
    _ = _ := by
      change (affinePullbackSectionsIso A B U).hom
          (algebraMap (((algΓ A).obj U).unop) (((algΓ A).obj U).unop ⊗[A] B) r) =
        (pullback.fst U.hom (baseMap A B)).appTop r at hl
      change (affinePullbackSectionsIso A B U).hom
          ((Algebra.TensorProduct.includeRight :
            B →ₐ[A] (((algΓ A).obj U).unop ⊗[A] B)) b) =
        ((Scheme.ΓSpecIso B).inv ≫
          (pullback.snd U.hom (baseMap A B)).appTop) b at hr
      exact (congrArg₂ (· * ·) hl hr).trans (mul_comm _ _)

theorem coefficientSectionsEquiv_eq_evaluation (U : Over (Spec A)) [IsAffine U.left]
    (w : B ⊗[A] ((algΓ A).obj U).unop) :
    coefficientSectionsEquiv A B U w =
      evaluationCoefficient A B (restrictedSections A B (coefficientTest A B U))
        (Algebra.TensorProduct.lTensor (S := B) B
          ((algΓ A).map (coefficientProjection A B U)).unop.hom w) := by
  induction w using TensorProduct.inductionOn with
  | tmul b r =>
    exact coefficientSectionsEquiv_tmul A B U b r
  | add w w' hw hw' => simp only [map_add, hw, hw']

variable [Module.Finite A B] [Module.Projective A B]

/-- Pull back a Weil point to the coefficient-ring test and evaluate it as a unit. -/
def coefficientEvaluation (U : Over (Spec A)) :
    (U ⟶ (groupScheme A B).X) →* Γ((coefficientTest A B U).left, ⊤)ˣ where
  toFun x := evaluationUnits A B (coefficientTest A B U) (coefficientProjection A B U ≫ x)
  map_one' := by
    rw [MonObj.comp_one]
    exact (evaluationUnits A B (coefficientTest A B U)).map_one
  map_mul' x y := by simp only [MonObj.comp_mul, map_mul]

theorem coefficientEvaluation_naturality {U U' : Over (Spec A)} (a : U' ⟶ U)
    (x : U ⟶ (groupScheme A B).X) :
    coefficientEvaluation A B U' (a ≫ x) =
      Units.map ((Over.pullback (baseMap A B)).map a).left.appTop.hom.toMonoidHom
        (coefficientEvaluation A B U x) := by
  change evaluationUnits A B _ (coefficientProjection A B U' ≫ (a ≫ x)) = _
  rw [← Category.assoc, ← coefficientProjection_naturality, Category.assoc]
  exact evaluationUnits_naturality A B ((Over.pullback (baseMap A B)).map a) _

/-- Affine pullback evaluation is an equivalence, with no flatness assumption on `B/A`. -/
def affineEvaluationEquiv (U : Over (Spec A)) [IsAffine U.left] :
    (U ⟶ (groupScheme A B).X) ≃* Γ((coefficientTest A B U).left, ⊤)ˣ :=
  (pointsEquiv A B U).trans
    (Units.mapEquiv (coefficientSectionsEquiv A B U).toMulEquiv)

theorem affineEvaluationEquiv_apply (U : Over (Spec A)) [IsAffine U.left]
    (x : U ⟶ (groupScheme A B).X) :
    affineEvaluationEquiv A B U x = coefficientEvaluation A B U x := by
  apply Units.ext
  change coefficientSectionsEquiv A B U (pointsEquiv A B U x).val = _
  rw [coefficientSectionsEquiv_eq_evaluation]
  change _ = evaluationCoefficient A B (restrictedSections A B (coefficientTest A B U))
    (pointsEquiv A B _ (coefficientProjection A B U ≫ x)).val
  rw [pointsEquiv_naturality]
  rfl

theorem affineEvaluationEquiv_naturality {U U' : Over (Spec A)}
    [IsAffine U.left] [IsAffine U'.left] (a : U' ⟶ U)
    (x : U ⟶ (groupScheme A B).X) :
    affineEvaluationEquiv A B U' (a ≫ x) =
      Units.map ((Over.pullback (baseMap A B)).map a).left.appTop.hom.toMonoidHom
        (affineEvaluationEquiv A B U x) := by
  simpa only [affineEvaluationEquiv_apply] using
    coefficientEvaluation_naturality A B a x

end Langlands.GroupScheme.WeilGm
