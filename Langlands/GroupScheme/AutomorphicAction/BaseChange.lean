import Langlands.GroupScheme.AutomorphicAction.Cocycles
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Base change of actual automorphic actions and base cocycles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S S' : Scheme.{u}} {H V : GroupScheme S}
    (a : AutomorphicAction H V) (b : S' ⟶ S)

/-- Pull back the action on actual points using the scheme pullback adjunction. -/
def baseChangeAct (T : Over S')
    (h : T ⟶ ((GroupScheme.baseChange b).obj H).X)
    (v : T ⟶ ((GroupScheme.baseChange b).obj V).X) :
    T ⟶ ((GroupScheme.baseChange b).obj V).X :=
  (baseChangePointsEquiv b V T).symm
    (a.act (baseChangePointsEquiv b H T h) (baseChangePointsEquiv b V T v))

theorem baseChangeAct_naturality {T W : Over S'} (f : W ⟶ T)
    (h : T ⟶ ((GroupScheme.baseChange b).obj H).X)
    (v : T ⟶ ((GroupScheme.baseChange b).obj V).X) :
    f ≫ a.baseChangeAct b T h v = a.baseChangeAct b W (f ≫ h) (f ≫ v) := by
  apply (baseChangePointsEquiv b V W).injective
  simp only [baseChangeAct, baseChangePointsEquiv_naturality,
    MulEquiv.apply_symm_apply, a.naturality]

/-- Base change of an automorphic action, with its actual action morphism. -/
def baseChange : AutomorphicAction ((GroupScheme.baseChange b).obj H)
    ((GroupScheme.baseChange b).obj V) :=
  ofPoints (a.baseChangeAct b) (a.baseChangeAct_naturality b)
    (fun T v => by simp only [baseChangeAct, map_one, a.act_one_left,
      MulEquiv.symm_apply_apply])
    (fun T h h' v => by
      apply (baseChangePointsEquiv b V T).injective
      simp only [baseChangeAct, MulEquiv.apply_symm_apply, map_mul, a.act_mul_left])
    (fun T h v v' => by
      apply (baseChangePointsEquiv b V T).injective
      simp only [baseChangeAct, MulEquiv.apply_symm_apply, map_mul, a.act_mul_right])

@[simp]
theorem baseChange_act {T : Over S'}
    (h : T ⟶ ((GroupScheme.baseChange b).obj H).X)
    (v : T ⟶ ((GroupScheme.baseChange b).obj V).X) :
    (a.baseChange b).act h v = a.baseChangeAct b T h v :=
  ofPoints_act _ _ _ _ _ h v

/-- The actual pullback point comparison intertwines the original and pulled-back actions. -/
theorem baseChangePointsEquiv_act {T : Over S'}
    (h : T ⟶ ((GroupScheme.baseChange b).obj H).X)
    (v : T ⟶ ((GroupScheme.baseChange b).obj V).X) :
    baseChangePointsEquiv b V T ((a.baseChange b).act h v) =
      a.act (baseChangePointsEquiv b H T h) (baseChangePointsEquiv b V T v) := by
  rw [baseChange_act, baseChangeAct, MulEquiv.apply_symm_apply]

namespace Cocycle

variable {a b}

/-- Restrict the acting group of a cocycle along an actual homomorphism. -/
def precomp {K : GroupScheme S} {T : Over S} (c : a.Cocycle T) (f : K ⟶ H) :
    (a.restrict f).Cocycle T where
  hom := (T ◁ f.hom.hom) ≫ c.hom
  one w := by
    simpa only [Category.assoc, lift_whiskerLeft_assoc, MonObj.one_comp] using c.one w
  mul w h h' := by
    simpa only [Category.assoc, lift_whiskerLeft_assoc, MonObj.mul_comp, restrict_act] using
      c.mul w (h ≫ f.hom.hom) (h' ≫ f.hom.hom)

@[simp]
theorem eval_precomp {K : GroupScheme S} {T W : Over S} (c : a.Cocycle T)
    (f : K ⟶ H) (w : W ⟶ T) (h : W ⟶ K.X) :
    (c.precomp f).eval w h = c.eval w (h ≫ f.hom.hom) := by
  simp only [eval, precomp, lift_whiskerLeft_assoc]

variable (b) (c : a.Cocycle (Over.mk (𝟙 S)))

/-- Pullback of a base cocycle evaluated on actual points. -/
def baseChangeEval (T : Over S')
    (h : T ⟶ ((GroupScheme.baseChange b).obj H).X) :
    T ⟶ ((GroupScheme.baseChange b).obj V).X :=
  (baseChangePointsEquiv b V T).symm
    (c.eval (Over.homMk (((Over.map b).obj T).hom) (by simp))
      (baseChangePointsEquiv b H T h))

theorem baseChangeEval_naturality {T W : Over S'} (f : W ⟶ T)
    (h : T ⟶ ((GroupScheme.baseChange b).obj H).X) :
    f ≫ c.baseChangeEval b T h = c.baseChangeEval b W (f ≫ h) := by
  apply (baseChangePointsEquiv b V W).injective
  simp only [baseChangeEval, baseChangePointsEquiv_naturality,
    MulEquiv.apply_symm_apply, c.eval_naturality]
  congr 1
  apply Over.OverMorphism.ext
  exact Over.w ((Over.map b).map f)

/-- Base change of a base-parametrized actual cocycle. -/
def baseChange : (a.baseChange b).Cocycle (Over.mk (𝟙 S')) where
  hom := snd _ _ ≫ c.baseChangeEval b _ (𝟙 _)
  one w := by
    rw [← Category.assoc, lift_snd, baseChangeEval_naturality, Category.comp_id]
    apply (baseChangePointsEquiv b V _).injective
    simp only [baseChangeEval, map_one, c.eval_one]
  mul w h h' := by
    simp only [lift_snd, baseChangeEval_naturality, Category.comp_id]
    apply (baseChangePointsEquiv b V _).injective
    simp only [baseChangeEval, MulEquiv.apply_symm_apply, map_mul,
      baseChangePointsEquiv_act, c.eval_mul]

@[simp]
theorem eval_baseChange {T : Over S'} (w : T ⟶ Over.mk (𝟙 S'))
    (h : T ⟶ ((GroupScheme.baseChange b).obj H).X) :
    (c.baseChange b).eval w h = c.baseChangeEval b T h := by
  simp only [eval, baseChange, lift_snd,
    baseChangeEval_naturality, Category.comp_id]

/-- Actual base change commutes with the coboundary of an actual base point. -/
theorem baseChange_coboundary (v : Over.mk (𝟙 S) ⟶ V.X) :
    (a.coboundary v).baseChange b =
      (a.baseChange b).coboundary (baseChangeBasePoint b V v) := by
  apply eval_ext
  intro T w h
  have hw : w = Over.homMk T.hom (by simp) := by
    apply Over.OverMorphism.ext
    simpa using w.w
  have hp : baseChangePointsEquiv b V T (w ≫ baseChangeBasePoint b V v) =
      Over.homMk (((Over.map b).obj T).hom) (by simp) ≫ v := by
    rw [hw]
    exact baseChangePointsEquiv_constantPoint b V v T
  rw [eval_baseChange]
  apply (baseChangePointsEquiv b V T).injective
  simp only [baseChangeEval, MulEquiv.apply_symm_apply, eval_coboundary,
    baseChangePointsEquiv_act, map_mul, map_inv, hp]

end Cocycle

end Langlands.GroupScheme.AutomorphicAction
