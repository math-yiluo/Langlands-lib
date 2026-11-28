import Langlands.GroupScheme.CocycleBaseChangeTriviality

/-! # Triviality after base change along a factored base map -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}

section Factor

variable {S₁ T : Scheme.{u}} (b : S₁ ⟶ S) (d : T ⟶ S) (e : S₁ ⟶ T) (hb : b = e ≫ d)

/-- The canonical map from the pulled-back cover along `b` to the pulled-back cover along `d`,
both viewed over `S`, when `b` factors through `d`. -/
def factorCoverProjection :
    (Over.map b).obj ((Over.pullback b).obj U) ⟶ (Over.map d).obj ((Over.pullback d).obj U) := by
  have he : (((Over.pullback b).obj U).hom ≫ e) ≫ d =
      ((Over.map b).obj ((Over.pullback b).obj U)).hom := by
    change (((Over.pullback b).obj U).hom ≫ e) ≫ d = ((Over.pullback b).obj U).hom ≫ b
    rw [hb, Category.assoc]
  refine Over.homMk (pullback.lift ((Over.mapPullbackAdj b).counit.app U).left
    (((Over.pullback b).obj U).hom ≫ e) ((Over.w ((Over.mapPullbackAdj b).counit.app U)).trans
      he.symm)) ?_
  change (pullback.lift _ _ _ ≫ pullback.snd U.hom d) ≫ d = _
  rw [pullback.lift_snd]
  exact he

theorem factorCoverProjection_comp :
    factorCoverProjection (U := U) b d e hb ≫ (Over.mapPullbackAdj d).counit.app U =
      (Over.mapPullbackAdj b).counit.app U := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

theorem factorCoverProjection_base :
    (factorCoverProjection (U := U) b d e hb).left ≫ ((Over.pullback d).obj U).hom =
      ((Over.pullback b).obj U).hom ≫ e :=
  pullback.lift_snd _ _ _

set_option maxHeartbeats 600000 in
include hb in
/-- If the base map `b` factors as `e ≫ d`, then triviality of the base change of a cocycle
along `d` implies triviality of its base change along `b`. -/
theorem isTrivial_baseChangePullback_of_factor (ξ : Cocycle G U)
    (h : (ξ.baseChangePullback d).IsTrivial) :
    (ξ.baseChangePullback b).IsTrivial := by
  obtain ⟨f, hf⟩ := ξ.exists_of_baseChange_isTrivial d ((Over.pullback d).obj U)
    ((Over.mapPullbackAdj d).counit.app U) h
  let τ := factorCoverProjection (U := U) b d e hb
  let g := (baseChangePointsEquiv b G ((Over.pullback b).obj U)).symm (τ ≫ f)
  refine ⟨g, fun {Z} x y => ?_⟩
  have hg (a : Z ⟶ (Over.pullback b).obj U) :
      baseChangePointsEquiv b G Z (a ≫ g) = (Over.map b).map a ≫ τ ≫ f := by
    rw [baseChangePointsEquiv_naturality]
    rw [show baseChangePointsEquiv b G ((Over.pullback b).obj U) g = τ ≫ f from
      (baseChangePointsEquiv b G _).apply_symm_apply _]
  have hab (a : Z ⟶ (Over.pullback b).obj U) :
      ((Over.map b).map a ≫ τ).left ≫ ((Over.pullback d).obj U).hom = Z.hom ≫ e := by
    change (a.left ≫ τ.left) ≫ ((Over.pullback d).obj U).hom = _
    rw [Category.assoc, factorCoverProjection_base, ← Category.assoc, Over.w a]
  have hxy := hf ((Over.map b).map x ≫ τ) ((Over.map b).map y ≫ τ)
    ((hab x).trans (hab y).symm)
  apply (baseChangePointsEquiv b G Z).injective
  rw [map_mul, map_inv, hg, hg]
  simp only [baseChangePullback, baseChange_toFun]
  simpa only [Category.assoc, τ, factorCoverProjection_comp] using hxy

end Factor

end Langlands.GroupScheme.Cocycle
