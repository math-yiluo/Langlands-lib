import Langlands.GroupScheme.CocycleAffineRefinement

/-! # Cover changes and base changes of trivial cocycles -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {G : GroupScheme S} {U V : Over S}

/-- The base change to a new base together with the canonical pullback cover. -/
def baseChangePullback (ξ : Cocycle G U) {S' : Scheme.{u}} (b : S' ⟶ S) :
    Cocycle ((GroupScheme.baseChange b).obj G) ((Over.pullback b).obj U) :=
  ξ.baseChange b _ ((Over.mapPullbackAdj b).counit.app U)

/-- A trivial cochain pulls back to every compatible cover over the new base. -/
theorem IsTrivial.baseChange {ξ : Cocycle G U} (h : ξ.IsTrivial) {S' : Scheme.{u}} (b : S' ⟶ S)
    (V : Over S') (r : (Over.map b).obj V ⟶ U) : (ξ.baseChange b V r).IsTrivial := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(baseChangePointsEquiv b G V).symm (r ≫ f), fun a c => ?_⟩
  apply (baseChangePointsEquiv b G _).injective
  simp only [baseChange_toFun, map_mul, map_inv, baseChangePointsEquiv_naturality,
    MulEquiv.apply_symm_apply, ← Category.assoc]
  exact hf _ _

section Square

set_option maxHeartbeats 600000

variable {S₁ S₂ T : Scheme.{u}} (b : S₁ ⟶ S) (c : S₂ ⟶ S₁)
    (d : T ⟶ S) (e : S₂ ⟶ T) (hc : c ≫ b = e ≫ d)

local notation "U₁" => (Functor.obj (Over.pullback b) U)
local notation "U₂" => (Functor.obj (Over.pullback c) U₁)
local notation "U₀" => (Functor.obj (Over.pullback d) U)
local notation "p" => (CategoryTheory.Functor.map (Over.map b)
  (NatTrans.app (Adjunction.counit (Over.mapPullbackAdj c)) U₁) ≫
  NatTrans.app (Adjunction.counit (Over.mapPullbackAdj b)) U)
local notation "M" => (Over.map c ⋙ Over.map b)

private def squareCoverProjection : (M).obj U₂ ⟶ (Over.map d).obj U₀ := by
  have he : ((U₂).hom ≫ e) ≫ d = ((M).obj U₂).hom := by
    change ((U₂).hom ≫ e) ≫ d = ((U₂).hom ≫ c) ≫ b
    simp only [Category.assoc, hc]
  refine Over.homMk (pullback.lift (p).left ((U₂).hom ≫ e) ((Over.w (p)).trans he.symm)) ?_
  change (pullback.lift _ _ _ ≫ pullback.snd U.hom d) ≫ d = _
  rw [pullback.lift_snd]
  exact he

private theorem squareCoverProjection_comp :
    squareCoverProjection (U := U) b c d e hc ≫ (Over.mapPullbackAdj d).counit.app U = (p) := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

private theorem squareCoverProjection_base :
    (squareCoverProjection (U := U) b c d e hc).left ≫ (U₀).hom = (U₂).hom ≫ e :=
  pullback.lift_snd _ _ _

include e hc in
/-- Triviality over one base in a commutative square implies triviality after the
successive pullbacks through the other base. -/
theorem isTrivial_baseChangePullback_twice (ξ : Cocycle G U)
    (h : (ξ.baseChangePullback d).IsTrivial) :
    ((ξ.baseChangePullback b).baseChangePullback c).IsTrivial := by
  obtain ⟨f, hf⟩ := ξ.exists_of_baseChange_isTrivial d U₀ ((Over.mapPullbackAdj d).counit.app U) h
  let G₁ := (GroupScheme.baseChange b).obj G
  let G₂ := (GroupScheme.baseChange c).obj G₁
  let τ := squareCoverProjection (U := U) b c d e hc
  let equiv (Z : Over S₂) : (Z ⟶ G₂.X) ≃* ((M).obj Z ⟶ G.X) :=
    (baseChangePointsEquiv c G₁ Z).trans (baseChangePointsEquiv b G ((Over.map c).obj Z))
  let g := (equiv U₂).symm (τ ≫ f)
  refine ⟨g, fun {Z} x y => ?_⟩
  have hg (a : Z ⟶ U₂) : equiv Z (a ≫ g) = (M).map a ≫ τ ≫ f := by
    change baseChangePointsEquiv b G _ (baseChangePointsEquiv c G₁ _ (a ≫ g)) = _
    rw [baseChangePointsEquiv_naturality, baseChangePointsEquiv_naturality]
    change (M).map a ≫ equiv U₂ g = _
    rw [show equiv U₂ g = τ ≫ f from (equiv U₂).apply_symm_apply _]
  have hab (a : Z ⟶ U₂) : ((M).map a ≫ τ).left ≫ (U₀).hom = Z.hom ≫ e := by
    change (a.left ≫ τ.left) ≫ (U₀).hom = _
    rw [Category.assoc, squareCoverProjection_base, ← Category.assoc, Over.w a]
  have hxy := hf ((M).map x ≫ τ) ((M).map y ≫ τ) ((hab x).trans (hab y).symm)
  apply (equiv Z).injective
  rw [map_mul, map_inv, hg, hg]
  change baseChangePointsEquiv b G _
      (baseChangePointsEquiv c G₁ _ (((ξ.baseChangePullback b).baseChangePullback c).toFun x y)) = _
  simp only [baseChangePullback, baseChange_toFun, Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_obj, Functor.comp_map, Category.assoc, τ,
    squareCoverProjection_comp] using hxy

end Square

end Langlands.GroupScheme.Cocycle
