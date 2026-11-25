/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionLocalBaseData
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Algebra.Homology.RingedSitePullback.PullbackLocalizationOfUniverses

/-! # The ordinary pullback mate on localized pro-étale module sites

## References

* Stacks Project, Modules on Sites, Tag 04J0
* Stacks Project, Modules on Sites, Tag 04J0, localization of a morphism of ringed sites
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

-- Compare the canonical mate with localization through its composite module adjunctions.
private theorem localizedInverseMate_isIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [Limits.HasFiniteLimits C] [Limits.HasFiniteLimits D] [Limits.PreservesFiniteLimits F]
    {R : Sheaf J RingCat.{u + 1}} {S : Sheaf K RingCat.{u + 1}}
    (a : R ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S)
    [(SheafOfModules.pushforward.{u + 1} a).IsRightAdjoint]
    (V : C) [(Over.post (X := V) F).IsContinuous (J.over V) (K.over (F.obj V))]
    (aV : R.over V ⟶ ((Over.post (X := V) F).sheafPushforwardContinuous RingCat
      (J.over V) (K.over (F.obj V))).obj (S.over (F.obj V)))
    [(SheafOfModules.pushforward.{u + 1} aV).IsRightAdjoint]
    (ha : aV = SheafOfModules.RingedSitePullback.locMap.{u + 1, u, 0} a V)
    (e : SheafOfModules.pushforward.{u + 1} a ⋙ SheafOfModules.overFunctor R V ≅
      SheafOfModules.overFunctor S (F.obj V) ⋙ SheafOfModules.pushforward aV)
    (he : ∀ (M : SheafOfModules.{u + 1} S) (T : (Over V)ᵒᵖ)
      (x : M.val.obj (op (F.obj T.unop.left))), ((e.hom.app M).val.app T) x = x) :
    IsIso (((mateEquiv (SheafOfModules.pullbackPushforwardAdjunction a)
      (SheafOfModules.pullbackPushforwardAdjunction aV)).symm
        (TwoSquare.mk _ _ _ _ e.hom))) := by
  subst aV
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hcomp : (((mateEquiv (SheafOfModules.pullbackPushforwardAdjunction a)
      (SheafOfModules.pullbackPushforwardAdjunction
        (SheafOfModules.RingedSitePullback.locMap.{u + 1, u, 0} a V))).symm
          (TwoSquare.mk _ _ _ _ e.hom))).app M =
      SheafOfModules.RingedSitePullback.localComparison.{u + 1, u, 0} a V M := by
    apply ((SheafOfModules.pullbackPushforwardAdjunction
      (SheafOfModules.RingedSitePullback.locMap.{u + 1, u, 0} a V)).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit]
    have hm := unit_mateEquiv_symm (SheafOfModules.pullbackPushforwardAdjunction a)
      (SheafOfModules.pullbackPushforwardAdjunction
        (SheafOfModules.RingedSitePullback.locMap.{u + 1, u, 0} a V))
      (TwoSquare.mk _ _ _ _ e.hom) M
    refine hm.symm.trans ?_
    erw [SheafOfModules.RingedSitePullback.localComparison, Equiv.apply_symm_apply]
    ext T x
    exact he ((SheafOfModules.pullback a).obj M) T
      (((SheafOfModules.pullbackPushforwardAdjunction a).unit.app M).val.app
        (op T.unop.left) x)
  rw [hcomp]
  infer_instance

/-- The inverse mate of the identity-on-sections direct-image square is invertible. -/
theorem localOrdinaryInverseMate_isIso
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X}
    (g : Global f R_Y R_X c) (V : Y.ProEt) (b : LocalBaseData g V)
    (ordinary : g.operation.pushforward ⋙
      SheafOfModules.overFunctor.{u + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V ≅
      SheafOfModules.overFunctor.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
        ((proEtaleBaseChange f).obj V) ⋙ b.operation.pushforward)
    (sections : ∀ (M : Mod R_X) (T : (Over V)ᵒᵖ)
      (x : M.val.obj (op ((proEtaleBaseChange f).obj T.unop.left))),
      ((ordinary.hom.app M).val.app T) x = x) :
    IsIso (((mateEquiv g.operation.moduleAdjunction b.operation.moduleAdjunction).symm
      (TwoSquare.mk _ _ _ _ ordinary.hom))) := by
  let := g.operation.continuous
  let := b.operation.continuous
  let := g.operation.rightAdjoint
  let := b.operation.rightAdjoint
  apply localizedInverseMate_isIso (proEtaleBaseChange f) g.operation.coefficient V
    b.operation.coefficient _ ordinary sections
  ext T x
  exact ConcreteCategory.congr_hom (b.coefficient_sections T.unop) x

end AlgebraicGeometry.Scheme.ProjectionRestriction
