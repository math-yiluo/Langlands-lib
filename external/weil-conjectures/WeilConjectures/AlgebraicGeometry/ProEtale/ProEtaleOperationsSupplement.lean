/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations

/-!
# Ordinary derived operations with identified pro-etale coefficients

## References

* Stacks Project, Modules on Sites, and Cohomology on Sites, Sections 07A5 and 0735
* Stacks, Section 07A5
* Stacks, Lemma 0DVC and Section 0735
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private noncomputable def proEtaleModuleModelEquivalence (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A) ≌
      SheafOfModules.{u + 1} A := by
  let B := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (proEtaleModelTopology X) := proEtaleModelUp_isContinuous X
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology X) (ProEt.topology X) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology X) (ProEt.topology X)
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)

private noncomputable def proEtaleScalarEquivalence (X : Scheme.{u})
    {A B : Sheaf (ProEt.topology X) RingCat.{u + 1}} (rc : A ≅ B) :
    SheafOfModules.{u + 1} B ≌ SheafOfModules.{u + 1} A := by
  let : (CategoryTheory.Equivalence.refl (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  let : (CategoryTheory.Equivalence.refl (C := X.ProEt)).inverse.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (J := ProEt.topology X) (K := ProEt.topology X) (S := A) (R := B)
    (CategoryTheory.Equivalence.refl (C := X.ProEt)) rc.hom rc.inv
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [B.obj.map_id]
      exact congrArg (fun q ↦ q.hom.app U) rc.inv_hom_id.symm)
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [A.obj.map_id, Category.comp_id]
      exact congrArg (fun q ↦ q.hom.app U) rc.hom_inv_id)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def proEtaleRingExtensionPresheaf
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ⥤
      PresheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj where
  obj := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom
  map a :=
    { app := fun U ↦ (ModuleCat.extendScalars (c.hom.hom.app U).hom).map (a.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality c.hom _ a }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    simp
    rfl
  map_comp a b := by
    apply PresheafOfModules.hom_ext
    intro U
    simp

private noncomputable def proEtaleRingExtension
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ⥤
      proEtaleRingModules X S :=
  proEtaleRingExtensionPresheaf f R S c ⋙ PresheafOfModules.sheafification
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)

private theorem proEtaleRingModuleDirectImage_isAdditive :
    (proEtaleRingModuleDirectImage f R S c).Additive := by
  constructor
  intro M N a b
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rfl

section

noncomputable local instance {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (M : proEtaleRingModules X A) {U V : X.ProEtᵒᵖ} (i : U ⟶ V) :
    Module (A.obj.obj V)
      ((ModuleCat.restrictScalars
        (((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj.map i).hom).obj
        (M.val.obj V)) :=
  inferInstanceAs (Module (A.obj.obj V) (M.val.obj V))

open scoped ChangeOfRings in
private theorem proEtale_changeOfRingsMap_tmul
    (M : proEtaleRingModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    {U V : X.ProEtᵒᵖ} (i : U ⟶ V) (s : S.obj.obj U) (m : M.val.obj U) :
    SheafOfModules.changeOfRingsMap c.hom M i
      (s ⊗ₜ[_, (c.hom.hom.app U).hom] m) =
      S.obj.map i s ⊗ₜ[_, (c.hom.hom.app V).hom] M.val.map i m :=
  Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap c.hom M i) s m

end

set_option backward.isDefEq.respectTransparency false in
open scoped ChangeOfRings in
private noncomputable def proEtaleExtensionToRestrict
    (M : proEtaleRingModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (N : proEtaleRingModules X S)
    (a : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom M ⟶ N.val) :
    M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj N where
  val.app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1, u + 1}
    (c.hom.hom.app U).hom (a.app U)
  val.naturality := by
    intro U V i
    ext m
    change a.app V ((1 : S.obj.obj V) ⊗ₜ[_, (c.hom.hom.app V).hom] M.val.map i m) =
      N.val.map i (a.app U ((1 : S.obj.obj U) ⊗ₜ[_, (c.hom.hom.app U).hom] m))
    rw [← PresheafOfModules.naturality_apply a i]
    change _ = a.app V (SheafOfModules.changeOfRingsMap c.hom M i _)
    rw [proEtale_changeOfRingsMap_tmul f R S c]
    simp only [map_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def proEtaleExtensionFromRestrict
    (M : proEtaleRingModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (N : proEtaleRingModules X S)
    (a : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj N) :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom M ⟶ N.val where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    (c.hom.hom.app U).hom (a.val.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      (c.hom.hom.app V).hom (a.val.app V)
        (SheafOfModules.changeOfRingsMap c.hom M i _) =
      N.val.map i
        (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
        (c.hom.hom.app U).hom (a.val.app U) _)
    rw [proEtale_changeOfRingsMap_tmul f R S c]
    simp only [map_one]
    let A := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
    let : Module (A.obj.obj V) (S.obj.obj V) :=
      Module.compHom (S.obj.obj V) (c.hom.hom.app V).hom
    let : Module (A.obj.obj V) (N.val.obj V) :=
      Module.compHom (N.val.obj V) (c.hom.hom.app V).hom
    let : Module (A.obj.obj U) (S.obj.obj U) :=
      Module.compHom (S.obj.obj U) (c.hom.hom.app U).hom
    let : Module (A.obj.obj U) (N.val.obj U) :=
      Module.compHom (N.val.obj U) (c.hom.hom.app U).hom
    erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      (R := A.obj.obj V) (S := S.obj.obj V), TensorProduct.lift.tmul,
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      (R := A.obj.obj U) (S := S.obj.obj U), TensorProduct.lift.tmul]
    change (1 : S.obj.obj V) • (show N.val.obj V from a.val.app V (M.val.map i m)) =
      N.val.map i ((1 : S.obj.obj U) • (show N.val.obj U from a.val.app U m))
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply a.val i m

private noncomputable def proEtaleExtensionHomEquiv
    (M : proEtaleRingModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (N : proEtaleRingModules X S) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom M ⟶ N.val) ≃
      (M ⟶ (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj N) where
  toFun := proEtaleExtensionToRestrict f R S c M N
  invFun := proEtaleExtensionFromRestrict f R S c M N
  left_inv a := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1}
      (c.hom.hom.app U).hom).left_inv _
  right_inv a := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1}
      (c.hom.hom.app U).hom).right_inv _

private noncomputable def proEtaleRingExtensionHomEquiv
    (M : proEtaleRingModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (N : proEtaleRingModules X S) :
    ((proEtaleRingExtension f R S c).obj M ⟶ N) ≃
      (M ⟶ (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj N) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).trans
    (proEtaleExtensionHomEquiv f R S c M N)

set_option backward.isDefEq.respectTransparency false in
open scoped ChangeOfRings in
private noncomputable def proEtaleRingExtensionAdjunction :
    proEtaleRingExtension f R S c ⊣
      SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom) := by
  let E := proEtaleRingExtension f R S c
  let T := SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)
  let e := proEtaleRingExtensionHomEquiv f R S c
  let adjS := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)
  have hnleft : ∀ M M' N (a : M ⟶ M') (b : E.obj M' ⟶ N),
      e M N (E.map a ≫ b) = a ≫ e M' N b := by
    intro M M' N a b
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    change (adjS.homEquiv _ _
      ((PresheafOfModules.sheafification _).map
        ((proEtaleRingExtensionPresheaf f R S c).map a) ≫ b)).app U
        ((1 : S.obj.obj U) ⊗ₜ[_, (c.hom.hom.app U).hom] m) =
      (adjS.homEquiv _ _ b).app U
        ((1 : S.obj.obj U) ⊗ₜ[_, (c.hom.hom.app U).hom] a.val.app U m)
    rw [adjS.homEquiv_naturality_left]
    change ((PresheafOfModules.sheafificationHomEquiv (𝟙 _)) b).app U
      ((ModuleCat.extendScalars (c.hom.hom.app U).hom).map (a.val.app U)
        ((1 : S.obj.obj U) ⊗ₜ[_, (c.hom.hom.app U).hom] m)) = _
    rw [ModuleCat.ExtendScalars.map_tmul]
    rfl
  have hnright : ∀ M N N' (a : N ⟶ N') (b : E.obj M ⟶ N),
      e M N' (b ≫ a) = e M N b ≫ T.map a := by
    intro M N N' a b
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    change (adjS.homEquiv _ _ (b ≫ a)).app U _ = _
    rw [adjS.homEquiv_naturality_right]
    rfl
  exact Adjunction.mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro M M' N a b
        apply (e M N).injective
        rw [Equiv.apply_symm_apply, hnleft, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun {M N N'} b a ↦ hnright M N N' a b }

private noncomputable def proEtaleModuleInverseImageAdjunction :
    proEtaleModuleInverseImage f R ⊣
      proEtaleRingModuleDirectImage f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) := by
  let A := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  let eY := proEtaleModuleModelEquivalence Y A
  let eX := proEtaleModuleModelEquivalence X B
  let adj := eY.symm.toAdjunction.comp
    ((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).comp
      eX.toAdjunction)
  change proEtaleModuleInverseImage f R ⊣ _ at adj
  apply adj.ofNatIsoRight
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    exact PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl)
  · intro M N a
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl

private noncomputable def proEtaleRingModulePullbackAdjunction :
    proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c := by
  let adj := (proEtaleModuleInverseImageAdjunction f R).comp
    (proEtaleRingExtensionAdjunction f R S c)
  change proEtaleRingModulePullback f R S c ⊣ _ at adj
  apply adj.ofNatIsoRight
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    exact PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl)
  · intro M N a
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl

private theorem proEtaleRingExtension_preservesFiniteLimits :
    PreservesFiniteLimits (proEtaleRingExtension f R S c) := by
  let rc := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let e := proEtaleScalarEquivalence X rc
  let T := SheafOfModules.restrictScalars rc.hom
  let : T.IsEquivalence := inferInstanceAs e.functor.IsEquivalence
  let adj := proEtaleRingExtensionAdjunction f R S c
  let ei := adj.leftAdjointUniq e.symm.toAdjunction
  exact preservesFiniteLimits_of_natIso ei.symm

private theorem proEtaleModuleInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (proEtaleModuleInverseImage f R) := by
  let A := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  let eY := proEtaleModuleModelEquivalence Y A
  let eX := proEtaleModuleModelEquivalence X B
  let L := SheafOfModules.pullback.{u + 1} (proEtaleModelRingUnit f R)
  let V := SheafOfModules.toSheaf
    (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj B)
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange f) := by
    change PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt) ⋙ proEtaleBaseChange f ⋙ AsSmall.up)
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange f) := flat_of_preservesFiniteLimits _
  obtain ⟨e⟩ := proEtaleModelModuleInverseImage_underlying f R
  let : PreservesFiniteLimits (L ⋙ V) := preservesFiniteLimits_of_natIso e.symm
  let : PreservesFiniteLimits L := preservesFiniteLimits_of_reflects_of_preserves L V
  let : PreservesFiniteLimits (proEtaleModuleToModel A) :=
    inferInstanceAs (PreservesFiniteLimits eY.inverse)
  let : PreservesFiniteLimits (proEtaleModuleFromModel B) :=
    inferInstanceAs (PreservesFiniteLimits eX.functor)
  change PreservesFiniteLimits (proEtaleModuleToModel A ⋙ L ⋙ proEtaleModuleFromModel B)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
attribute [instance] proEtaleRingModules_hasKInjectiveResolutions

/-- Ordinary uncompleted unbounded derived direct image via K-injectives in all modules. -/
noncomputable abbrev proEtaleRingDerivedDirectImage :
    DerivedCategory (proEtaleRingModules X S) ⥤ DerivedCategory (proEtaleRingModules Y R) :=
  (proEtaleRingModuleDirectImage f R S c).rightDerivedFunctor

/-- Direct image is computed on every K-injective representative, naturally in that
representative. -/
theorem proEtaleRingDerivedDirectImage_kInjective
    (I : CochainComplex (proEtaleRingModules X S) ℤ) [I.IsKInjective] :
    IsIso ((proEtaleRingModuleDirectImage f R S c).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I)) := by
  infer_instance


/-- The ordinary derived adjunction on the full unbounded derived categories. -/
theorem proEtaleRingDerivedOperations_adjunction :
    Nonempty (proEtaleRingDerivedPullback f R S c ⊣ proEtaleRingDerivedDirectImage f R S c) := by
  obtain ⟨adj⟩ := (proEtaleRingModuleOperations_properties f R S c).2.2.2.2
  exact ⟨adj.mapDerivedCategoryRightDerivedAdjunction⟩

end AlgebraicGeometry.Scheme
