import Langlands.GroupScheme.Reductive.AffinePinnedCoefficientPinning
import Langlands.GroupScheme.Reductive.AffinePinnedInnerPinning

/-! # Normalized affine points of direct pullbacks -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

local instance (M : AffinePinnedModel.{u}) (A : Type u)
    [CommRing A] [Algebra M.ring A] :
    IsAffineHom (M.groupOver (algebraBaseMap M.ring A)).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd M.group.X.hom (algebraBaseMap M.ring A)))

variable (M : AffinePinnedModel.{u}) (A : Type u) [CommRing A]
  [Algebra M.ring A] {W : Scheme.{u}} (p : W ⟶ Spec (CommRingCat.of A))

/-- Direct normalized sections project multiplicatively to the scalar model. -/
def normalizedBasePointsEquiv :
    (Over.mk (𝟙 W) ⟶ (M.groupOver (p ≫ algebraBaseMap M.ring A)).X) ≃*
      (Over.mk p ⟶ (M.groupOver (algebraBaseMap M.ring A)).X) := by
  let E : (Over.mk (𝟙 W) ⟶ (M.groupOver (p ≫ algebraBaseMap M.ring A)).X) ≃*
      (Over.mk (𝟙 W) ⟶ ((baseChange p).obj
        (M.groupOver (algebraBaseMap M.ring A))).X) :=
    { toFun := fun x => x ≫ (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom.hom.hom
      invFun := fun x => x ≫ (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).inv.hom.hom
      left_inv := fun x => by
        dsimp only
        rw [Category.assoc]
        change x ≫ ((baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom ≫
          (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).inv).hom.hom = x
        simp
      right_inv := fun x => by
        dsimp only
        rw [Category.assoc]
        change x ≫ ((baseChangeCompIso (algebraBaseMap M.ring A) p M.group).inv ≫
          (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom).hom.hom = x
        simp
      map_mul' := fun x y => MonObj.mul_comp _ _ _ }
  exact E.trans (baseChangeBasePointsEquiv p (M.groupOver (algebraBaseMap M.ring A)))

@[simp] theorem normalizedBasePointsEquiv_left
    (x : Over.mk (𝟙 W) ⟶ (M.groupOver (p ≫ algebraBaseMap M.ring A)).X) :
    (normalizedBasePointsEquiv M A p x).left = x.left ≫
      (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom.hom.hom.left ≫
        pullback.fst (M.groupOver (algebraBaseMap M.ring A)).X.hom p := by
  rfl

local instance (B : Type u) [CommRing B] [Algebra A B] :
    Algebra (M.scalarExtension A).ring B := inferInstanceAs (Algebra A B)

variable (B : Type u) [CommRing B] [Algebra A B]
  (a : Spec (CommRingCat.of B) ⟶ W)
  (hA : algebraBaseMap A B = a ≫ p)

/-- Direct normalized test points, viewed as actual affine scalar-model points. -/
def normalizedTestPointsEquiv :
    (Over.mk a ⟶ (M.groupOver (p ≫ algebraBaseMap M.ring A)).X) ≃*
      Lie.AffinePoints (M.groupOver (algebraBaseMap M.ring A)) B := by
  let E : (Over.mk a ⟶ (M.groupOver (p ≫ algebraBaseMap M.ring A)).X) ≃*
      (Over.mk a ⟶ ((baseChange p).obj
        (M.groupOver (algebraBaseMap M.ring A))).X) :=
    { toFun := fun x => x ≫ (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom.hom.hom
      invFun := fun x => x ≫ (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).inv.hom.hom
      left_inv := fun x => by
        dsimp only
        rw [Category.assoc]
        change x ≫ ((baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom ≫
          (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).inv).hom.hom = x
        simp
      right_inv := fun x => by
        dsimp only
        rw [Category.assoc]
        change x ≫ ((baseChangeCompIso (algebraBaseMap M.ring A) p M.group).inv ≫
          (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom).hom.hom = x
        simp
      map_mul' := fun x y => MonObj.mul_comp _ _ _ }
  exact E.trans (coefficientTestPointsEquiv (M := M.scalarExtension A) p B a hA
        (M.groupOver (algebraBaseMap M.ring A)))

@[simp] theorem normalizedTestPointsEquiv_left
    (x : Over.mk a ⟶ (M.groupOver (p ≫ algebraBaseMap M.ring A)).X) :
    (normalizedTestPointsEquiv M A p B a hA x).left = x.left ≫
      (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom.hom.hom.left ≫
        pullback.fst (M.groupOver (algebraBaseMap M.ring A)).X.hom p := by
  change (x.left ≫
    (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom.hom.hom.left) ≫ _ = _
  exact Category.assoc _ _ _

/-- Constant families project to the supplied section on every affine test. -/
theorem normalizedTestPointsEquiv_constant
    (z : Over.mk (𝟙 W) ⟶ (M.groupOver (p ≫ algebraBaseMap M.ring A)).X) :
    normalizedTestPointsEquiv M A p B a hA
      ((M.groupOver (p ≫ algebraBaseMap M.ring A)).constantPoint z (Over.mk a)) =
    (coefficientTestIso (M := M.scalarExtension A) p B a hA).hom ≫
      (Over.homMk (U := Over.mk (a ≫ p)) (V := Over.mk p) a rfl) ≫ normalizedBasePointsEquiv M A p z := by
  apply Over.OverMorphism.ext
  simp only [normalizedTestPointsEquiv_left, normalizedBasePointsEquiv_left,
    constantPoint, Over.comp_left]
  change (a ≫ z.left) ≫ _ ≫ _ = 𝟙 _ ≫ a ≫ _
  simp only [Category.id_comp, Category.assoc]

/-- The normalized projection identifies every original pinning point with
coefficient extension of the scalar model's chosen vector. -/
theorem normalizedTestPointsEquiv_rootVector
    [Algebra M.ring B] [IsScalarTower M.ring A B]
    (hb : algebraBaseMap M.ring B = a ≫ (p ≫ algebraBaseMap M.ring A))
    (s : M.basis.support) :
    normalizedTestPointsEquiv M A p (DualNumber B)
      (algebraBaseMap B (DualNumber B) ≫ a)
      (dualNumber_test_base (M := M.scalarExtension A) p B a hA)
      (Over.homMk (M.rootVectorPoint (p ≫ algebraBaseMap M.ring A) B a hb s)
        (M.rootVectorPoint_snd _ _ _ hb s)) =
      (lieKernelMapLinear (M.groupOver (algebraBaseMap M.ring A)) (Algebra.ofId A B)
        ((M.scalarExtension A).pinning s 1).val).toMul.val := by
  apply Over.OverMorphism.ext
  rw [normalizedTestPointsEquiv_left]
  change M.rootVectorPoint (p ≫ algebraBaseMap M.ring A) B a hb s ≫
    (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom.hom.hom.left ≫
      pullback.fst (M.groupOver (algebraBaseMap M.ring A)).X.hom p = _
  rw [M.rootVectorPoint_pull]
  exact (M.scalarExtension_pinning_map_point A B (a ≫ p) hA
    (by simpa only [Category.assoc] using hb) s).symm

variable {N : AffinePinnedModel.{u}} [Algebra N.ring A]

/-- Projection of a normalized pulled comparison is the original comparison. -/
theorem normalizedTestPointsEquiv_pullComparison
    (e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A))
    (x : Over.mk a ⟶ (M.groupOver (p ≫ algebraBaseMap M.ring A)).X) :
    normalizedTestPointsEquiv N A p B a hA (x ≫ (pullComparison e p).hom.hom.hom) =
      normalizedTestPointsEquiv M A p B a hA x ≫ e.hom.hom.hom := by
  have heq : (pullComparison e p).hom ≫
      (baseChangeCompIso (algebraBaseMap N.ring A) p N.group).hom =
    (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom ≫ (baseChange p).map e.hom := by
    simp [pullComparison]
  have heq' := congrArg (fun k => k.hom.hom.left) heq
  change (pullComparison e p).hom.hom.hom.left ≫
      (baseChangeCompIso (algebraBaseMap N.ring A) p N.group).hom.hom.hom.left =
    (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom.hom.hom.left ≫
      ((baseChange p).map e.hom).hom.hom.left at heq'
  have hm : ((baseChange p).map e.hom).hom.hom.left ≫
      pullback.fst (N.groupOver (algebraBaseMap N.ring A)).X.hom p =
    pullback.fst (M.groupOver (algebraBaseMap M.ring A)).X.hom p ≫ e.hom.hom.hom.left :=
    pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  simp only [normalizedTestPointsEquiv_left, Over.comp_left, Category.assoc]
  rw [← Category.assoc (pullComparison e p).hom.hom.hom.left, heq', Category.assoc, hm]

/-- The normalized affine-test projection has the expected two-step first projection. -/
def NormalizedPointProjectionCriterion : Prop :=
  ∀ (M : AffinePinnedModel.{u}) (A : Type u) [CommRing A] [Algebra M.ring A]
    (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of A))
    (B : Type u) [CommRing B] [Algebra A B]
    (a : Spec (CommRingCat.of B) ⟶ W) (hA : algebraBaseMap A B = a ≫ p)
    (x : Over.mk a ⟶ (M.groupOver (p ≫ algebraBaseMap M.ring A)).X),
    (normalizedTestPointsEquiv M A p B a hA x).left = x.left ≫
      (baseChangeCompIso (algebraBaseMap M.ring A) p M.group).hom.hom.hom.left ≫
        pullback.fst (M.groupOver (algebraBaseMap M.ring A)).X.hom p

theorem normalizedPointProjectionCriterion : NormalizedPointProjectionCriterion.{u} :=
  fun M A _ _ _W p B _ _ a hA x => normalizedTestPointsEquiv_left M A p B a hA x

end Langlands.GroupScheme.AffinePinnedModel
