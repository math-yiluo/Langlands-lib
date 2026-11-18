import Langlands.GroupScheme.RelativeUnipotent.SourceFreeSectionReconstruction
import Langlands.GroupScheme.RelativeUnipotent.VectorBundleBaseChangeCocycle

/-! # Natural linear transformations of actual pulled-back module sections -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.NaturalModuleTransformations

variable {S : Scheme.{u}}

/-- The actual module isomorphism acts linearly on its global sections. -/
def sectionLinearEquiv {M N : S.Modules} (e : M ≅ N) :
    GlobalSections M ≃ₗ[Γ(S, ⊤)] GlobalSections N :=
  { (e.hom.app ⊤).hom with
    map_smul' := fun r x => e.hom.app_smul r x
    invFun := e.inv.app ⊤
    left_inv := fun x => by
      change (e.hom ≫ e.inv).app ⊤ x = x
      rw [e.hom_inv_id]
      rfl
    right_inv := fun x => by
      change (e.inv ≫ e.hom).app ⊤ x = x
      rw [e.inv_hom_id]
      rfl }

/-- The linear form of the prescribed actual pullback-composition comparison. -/
def baseChangeLinearEquiv {X : Scheme.{u}} (b : X ⟶ S) (M : S.Modules)
    (T : Over X) :
    GlobalSections ((Scheme.Modules.pullback T.hom).obj
      ((Scheme.Modules.pullback b).obj M)) ≃ₗ[Γ(T.left, ⊤)]
      GlobalSections ((Scheme.Modules.pullback ((Over.map b).obj T).hom).obj M) :=
  sectionLinearEquiv ((Scheme.Modules.pullbackComp T.hom b).app M)

lemma baseChangeLinearEquiv_apply {X : Scheme.{u}} (b : X ⟶ S)
    (M : S.Modules) (T : Over X) (x) :
    baseChangeLinearEquiv b M T x = baseChangeSectionEquiv b M T x := rfl

lemma baseChangeLinearEquiv_symm_apply {X : Scheme.{u}} (b : X ⟶ S)
    (M : S.Modules) (T : Over X) (x) :
    (baseChangeLinearEquiv b M T).symm x = (baseChangeSectionEquiv b M T).symm x := by
  apply (baseChangeSectionEquiv b M T).injective
  change (baseChangeLinearEquiv b M T) ((baseChangeLinearEquiv b M T).symm x) = _
  rw [LinearEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Actual linear maps of pullback sections, natural on all scheme tests. -/
structure Transformation (M N : S.Modules) where
  app : ∀ T : Over S,
    GlobalSections ((Scheme.Modules.pullback T.hom).obj M) →ₗ[Γ(T.left, ⊤)]
      GlobalSections ((Scheme.Modules.pullback T.hom).obj N)
  natural : ∀ (T W : Over S) (b : W ⟶ T)
    (x : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)),
    app W (sectionPullback M b x) = sectionPullback N b (app T x)

namespace Transformation

variable {M N P : S.Modules}

/-- Pullback sections of an actual sheaf morphism form a natural linear transformation. -/
def ofHom (f : M ⟶ N) : Transformation M N where
  app T := {
    __ := (((Scheme.Modules.pullback T.hom).map f).app ⊤).hom
    map_smul' := fun r x => ((Scheme.Modules.pullback T.hom).map f).app_smul r x }
  natural T W b x := by
    let comparisonNat := (Scheme.Modules.pullbackComp b.left T.hom).hom ≫
      (Scheme.Modules.pullbackCongr (Over.w b)).hom
    change ((Scheme.Modules.pullback W.hom).map f).app ⊤
        ((comparisonNat.app M).app ⊤ (pullbackSection b.left _ x)) =
      (comparisonNat.app N).app ⊤ (pullbackSection b.left _
        (((Scheme.Modules.pullback T.hom).map f).app ⊤ x))
    rw [pullbackSection_naturality]
    change (comparisonNat.app M ≫ (Scheme.Modules.pullback W.hom).map f).app ⊤
        (pullbackSection b.left _ x) =
      ((Scheme.Modules.pullback b.left).map ((Scheme.Modules.pullback T.hom).map f) ≫
        comparisonNat.app N).app ⊤ (pullbackSection b.left _ x)
    exact congrArg (fun g => g.app ⊤ (pullbackSection b.left _ x))
      (comparisonNat.naturality f).symm

/-- Composition retains the original natural section maps. -/
def comp (C : Transformation M N) (D : Transformation N P) : Transformation M P where
  app T := (D.app T).comp (C.app T)
  natural T W b x := by
    change D.app W (C.app W (sectionPullback M b x)) = _
    rw [C.natural, D.natural]
    rfl

/-- Restrict a natural section transformation to any base scheme, using the
canonical actual pullback-composition comparisons. -/
def baseChange (C : Transformation M N) {X : Scheme.{u}} (b : X ⟶ S) :
    Transformation ((Scheme.Modules.pullback b).obj M) ((Scheme.Modules.pullback b).obj N) where
  app T := ((baseChangeLinearEquiv b N T).symm.toLinearMap).comp
    ((C.app ((Over.map b).obj T)).comp (baseChangeLinearEquiv b M T).toLinearMap)
  natural T W a x := by
    change (baseChangeLinearEquiv b N W).symm
        (C.app ((Over.map b).obj W)
          (baseChangeLinearEquiv b M W
            (sectionPullback ((Scheme.Modules.pullback b).obj M) a x))) = _
    simp only [baseChangeLinearEquiv_apply, baseChangeLinearEquiv_symm_apply]
    rw [baseChangeSectionEquiv_naturality, C.natural,
      baseChangeSectionEquiv_symm_naturality]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      baseChangeLinearEquiv_apply, baseChangeLinearEquiv_symm_apply]

/-- Regard free-source sections as coordinates for the actual transformation. -/
def freeCoordinates {n : ℕ} (C : Transformation (freeBundle S n) N) :
    SourceFreeSectionReconstruction.Transformation n N where
  app T := (C.app T).comp (freeBundleBasis n T).equivFun.symm.toLinearMap
  natural T W b x := by
    change C.app W (freeBundleSectionEquiv n W (fun i => b.left.appTop (x i))) = _
    rw [freeBundleSectionEquiv_natural, C.natural]
    rfl

/-- The natural transformation with a free source constructs an actual sheaf map. -/
def reconstructFree {n : ℕ} (C : Transformation (freeBundle S n) N) :
    freeBundle S n ⟶ N :=
  C.freeCoordinates.moduleHom

/-- The reconstructed actual map recovers the original transformation on
all sections of all scheme tests. -/
lemma reconstructFree_apply {n : ℕ} (C : Transformation (freeBundle S n) N)
    (T : Over S) (x : GlobalSections
      ((Scheme.Modules.pullback T.hom).obj (freeBundle S n))) :
    ((Scheme.Modules.pullback T.hom).map C.reconstructFree).app ⊤ x = C.app T x := by
  obtain ⟨v, rfl⟩ := (freeBundleSectionEquiv n T).surjective x
  exact C.freeCoordinates.moduleHom_coordinates T v

end Transformation
end Langlands.GroupScheme.RelativeUnipotent.NaturalModuleTransformations
