/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Exact constant-coefficient pullback in independent universes

## References

* Stacks Project, Tags 00YV, 03D2, and 04JC
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe t r
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.Scheme

private abbrev Site (X : Scheme.{t}) := coefficientProEtaleSiteModel.{t, r} X
private abbrev Top (X : Scheme.{t}) := coefficientProEtaleModelTopology.{t, r} X
private abbrev Base {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  coefficientProEtaleModelBaseChange.{t, r} f

private instance (X : Scheme.{t}) :
    (AsSmall.down : Site.{t,r} X ⥤ X.ProEt).IsEquivalence :=
  inferInstanceAs (AsSmall.equiv.{t, t + 1, max r (t + 1)} (C := X.ProEt)).inverse.IsEquivalence

private instance (X : Scheme.{t}) :
    (AsSmall.up : X.ProEt ⥤ Site.{t,r} X).IsEquivalence :=
  inferInstanceAs (AsSmall.equiv.{t, t + 1, max r (t + 1)} (C := X.ProEt)).functor.IsEquivalence

private def modelEquivalence (X : Scheme.{t}) (D : Type*) [Category.{max r (t + 1)} D] :
    Sheaf (Top.{t,r} X) D ≌ Sheaf (ProEt.topology X) D :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ Site.{t,r} X).sheafPushforwardContinuous D
      (ProEt.topology X) (Top X))
    ((AsSmall.down : Site.{t,r} X ⥤ X.ProEt).sheafPushforwardContinuous D
      (Top X) (ProEt.topology X)) (Iso.refl _) (Iso.refl _)

private def modelConstantAdjunction (X : Scheme.{t})
    (D : Type*) [Category.{max r (t + 1)} D]
    [HasWeakSheafify (ProEt.topology X) D]
    {T : X.ProEt} (hT : IsTerminal T) :
    constantSheaf (ProEt.topology X) D ⋙ (modelEquivalence X D).inverse ⊣
      (sheafSections (Top.{t,r} X) D).obj (op (AsSmall.up.obj T)) :=
  (constantSheafAdj (ProEt.topology X) D hT).comp
    (modelEquivalence X D).symm.toAdjunction

private def modelCommRingMap {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    (modelEquivalence Y CommRingCat.{max r (t + 1)}).inverse.obj
      ((constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).obj A) ⟶
    ((Base.{t,r} f).sheafPushforwardContinuous CommRingCat.{max r (t + 1)}
      (Top Y) (Top X)).obj
        ((modelEquivalence X CommRingCat.{max r (t + 1)}).inverse.obj
          ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A)) :=
  ⟨Functor.whiskerLeft AsSmall.down.op (coefficientProEtaleDirectRingMap f A).hom⟩

private theorem modelCommRingMapAdjunct_isIso {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    IsIso (((sheafAdjunctionContinuous (Base.{t,r} f) CommRingCat.{max r (t + 1)}
      (Top Y) (Top X)).homEquiv _ _).symm (modelCommRingMap f A)) := by
  let D := CommRingCat.{max r (t + 1)}
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  let hGT := hT.isTerminalObj (proEtaleBaseChange f) _
  let aY := modelConstantAdjunction.{t,r} Y D hT
  let aX := modelConstantAdjunction.{t,r} X D hGT
  let a : (constantSheaf (ProEt.topology Y) D ⋙
      (modelEquivalence Y D).inverse) ⋙ sheafPullback (Base.{t,r} f) D (Top Y) (Top X) ⊣
      (sheafSections (Top.{t,r} X) D).obj
        (op (AsSmall.up.obj ((proEtaleBaseChange f).obj T))) :=
    (aY.comp (sheafAdjunctionContinuous (Base.{t,r} f) D (Top Y) (Top X))).ofNatIsoRight
      (Iso.refl _)
  let e := a.leftAdjointUniq aX
  have he : ((sheafAdjunctionContinuous (Base.{t,r} f) D (Top Y) (Top X)).homEquiv
      _ _).symm (modelCommRingMap f A) = e.hom.app A := by
    apply (a.homEquiv _ _).injective
    apply Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app a aX A).symm
    change (aY.homEquiv _ _)
      (((sheafAdjunctionContinuous (Base.{t,r} f) D (Top Y) (Top X)).homEquiv _ _)
        (((sheafAdjunctionContinuous (Base.{t,r} f) D (Top Y) (Top X)).homEquiv
          _ _).symm (modelCommRingMap f A))) = aX.unit.app A
    rw [Equiv.apply_symm_apply]
    dsimp [aY, modelConstantAdjunction]
    rw [Adjunction.comp_homEquiv]
    change (constantSheafAdj (ProEt.topology Y) D hT).homEquiv _ _
      (coefficientProEtaleDirectRingMap f A) = _
    dsimp [coefficientProEtaleDirectRingMap]
    rw [constantSheafAdj, Adjunction.comp_homEquiv]
    change (constantPresheafAdj D hT).homEquiv _ _
      (((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _)
        (((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

private abbrev ring (X : Scheme.{t}) (A : CommRingCat.{max r (t + 1)}) :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A)

private theorem modelRingPresentation {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    ∃ p : SheafPullbackUnitPresentation (F := Base.{t,r} f)
      ((sheafCompose (Top.{t,r} Y) (CategoryTheory.forget RingCat.{max r (t + 1)})).obj
        ((modelEquivalence Y RingCat.{max r (t + 1)}).inverse.obj (ring Y A)))
      ((sheafCompose (Top.{t,r} X) (CategoryTheory.forget RingCat.{max r (t + 1)})).obj
        ((modelEquivalence X RingCat.{max r (t + 1)}).inverse.obj (ring X A))),
      p.unit = (sheafCompose (Top.{t,r} Y) (CategoryTheory.forget RingCat.{max r (t + 1)})).map
        (coefficientProEtaleModelRingMap.{t,r} f A) := by
  let F := Base.{t,r} f
  let J := Top.{t,r} Y
  let K := Top.{t,r} X
  let S := (modelEquivalence Y CommRingCat.{max r (t + 1)}).inverse.obj
    ((constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).obj A)
  let adj := sheafAdjunctionContinuous F CommRingCat.{max r (t + 1)} J K
  let c := (adj.homEquiv _ _).symm (modelCommRingMap f A)
  have : IsIso c := modelCommRingMapAdjunct_isIso f A
  have : PreservesFiniteLimits F := by
    dsimp [F, Base, coefficientProEtaleModelBaseChange]
    infer_instance
  have : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let U := CategoryTheory.forget CommRingCat.{max r (t + 1)}
  let ec := (sheafCompose K U).mapIso (asIso c).symm
  let e := ec ≪≫ (sheafPullbackForgetIso J K F U).app S
  let unit := (sheafCompose (Top.{t,r} Y) (CategoryTheory.forget RingCat.{max r (t + 1)})).map
    (coefficientProEtaleModelRingMap.{t,r} f A)
  refine ⟨⟨unit, e, ?_⟩, rfl⟩
  intro V x
  have hc := (adj.homEquiv _ _).apply_symm_apply (modelCommRingMap f A)
  rw [Adjunction.homEquiv_unit] at hc
  have hcx := congrArg (fun z ↦ z.hom.app V x) hc
  have hu := sheafPullbackForgetIso_unit J K F U S
  have hux := congrArg (fun z ↦ z.hom.app V x) hu
  change ((sheafPullbackForgetIso J K F U).hom.app S).hom.app (F.op.obj V)
    ((asIso c).inv.hom.app (F.op.obj V) (unit.hom.app V x)) = _
  have hinv : (asIso c).inv.hom.app (F.op.obj V) (unit.hom.app V x) =
      (adj.unit.app S).hom.app V x := by
    change c.hom.app (F.op.obj V) ((adj.unit.app S).hom.app V x) = unit.hom.app V x at hcx
    exact (congrArg (fun y ↦ (asIso c).inv.hom.app (F.op.obj V) y) hcx.symm).trans
      (ConcreteCategory.congr_hom
        (congrArg (fun z ↦ z.hom.app (F.op.obj V)) (asIso c).hom_inv_id) _)
  rw [hinv]
  exact hux

private def moduleEquivalence (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}) :
    SheafOfModules.{max r (t + 1)}
      ((modelEquivalence X RingCat.{max r (t + 1)}).inverse.obj R) ≌
        SheafOfModules.{max r (t + 1)} R := by
  let B := (modelEquivalence X RingCat.{max r (t + 1)}).inverse.obj R
  let : (AsSmall.equiv.{t, t + 1, max r (t + 1)} (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (Top.{t,r} X) := coefficientProEtaleModelUp_isContinuous X
  let : (AsSmall.equiv.{t, t + 1, max r (t + 1)} (C := X.ProEt)).inverse.IsContinuous
      (Top.{t,r} X) (ProEt.topology X) := by
    change AsSmall.down.IsContinuous (Top.{t,r} X) (ProEt.topology X)
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{t, t + 1, max r (t + 1)} (C := X.ProEt)) (𝟙 R) (𝟙 B)
    (by ext V; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext V; dsimp [AsSmall.equiv]; erw [R.obj.map_id]; rfl)

private theorem modelPullback_exact {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    PreservesFiniteLimits (SheafOfModules.pullback.{max r (t + 1)}
      (coefficientProEtaleModelRingMap.{t,r} f A)) ∧
    PreservesFiniteColimits (SheafOfModules.pullback.{max r (t + 1)}
      (coefficientProEtaleModelRingMap.{t,r} f A)) := by
  have : PreservesFiniteLimits (Base.{t,r} f) := by
    dsimp [Base, coefficientProEtaleModelBaseChange]
    infer_instance
  have : RepresentablyFlat (Base.{t,r} f) := flat_of_preservesFiniteLimits _
  obtain ⟨p, hp⟩ := modelRingPresentation f A
  obtain ⟨e, _⟩ := SheafOfModules.inverseImage_underlying_of_ring_presentation
    (coefficientProEtaleModelRingMap.{t,r} f A) p hp
  let M := SheafOfModules.pullback.{max r (t + 1)} (coefficientProEtaleModelRingMap.{t,r} f A)
  let U := SheafOfModules.toSheaf.{max r (t + 1)}
    ((modelEquivalence X RingCat.{max r (t + 1)}).inverse.obj (ring X A))
  have (Z : Scheme.{t}) : HasSheafify (Top.{t,r} Z) AddCommGrpCat.{max r (t + 1)} :=
    inferInstance
  have (Z : Scheme.{t}) : (Top.{t,r} Z).WEqualsLocallyBijective
      AddCommGrpCat.{max r (t + 1)} := inferInstance
  let La := sheafPullback (Base.{t,r} f) AddCommGrpCat.{max r (t + 1)} (Top Y) (Top X)
  have : PreservesColimitsOfSize.{0,0} La :=
    (sheafAdjunctionContinuous (Base.{t,r} f) AddCommGrpCat.{max r (t + 1)}
      (Top Y) (Top X)).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0,0} U := ⟨fun {J} _ ↦ inferInstance⟩
  have : ReflectsColimitsOfSize.{0,0} U := reflectsColimits_of_reflectsIsomorphisms
  have : PreservesFiniteLimits (M ⋙ U) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (M ⋙ U) := preservesFiniteColimits_of_natIso e.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves M U,
    preservesFiniteColimits_of_reflects_of_preserves M U⟩

/-- Constant-coefficient module pullback is exact, with no relation imposed between
site and coefficient universes. -/
theorem coefficientProEtaleModulePullback_exact {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    PreservesFiniteLimits (coefficientProEtaleModulePullback.{t,r} f A) ∧
      PreservesFiniteColimits (coefficientProEtaleModulePullback.{t,r} f A) := by
  let EY := moduleEquivalence.{t,r} Y (ring Y A)
  let EX := moduleEquivalence.{t,r} X (ring X A)
  let M := SheafOfModules.pullback.{max r (t + 1)} (coefficientProEtaleModelRingMap.{t,r} f A)
  have hm := modelPullback_exact f A
  have : PreservesFiniteLimits M := hm.1
  have : PreservesFiniteColimits M := hm.2
  let adj := (EY.symm.toAdjunction.comp
    (SheafOfModules.pullbackPushforwardAdjunction (coefficientProEtaleModelRingMap.{t,r} f A))).comp
      EX.toAdjunction
  let eR : EX.inverse ⋙ SheafOfModules.pushforward.{max r (t + 1)}
      (coefficientProEtaleModelRingMap.{t,r} f A) ⋙ EY.functor ≅
        coefficientProEtaleModuleDirectImage.{t,r} f A := by
    refine NatIso.ofComponents (fun N ↦ ?_) ?_
    · exact (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun V ↦ ModuleCat.isoMk (Iso.refl _)
          (by intro a; ext x; rfl)) (by intros; ext x; rfl))
    · intros
      ext V x
      rfl
  let e := (coefficientProEtaleModuleAdjunction f A).leftAdjointUniq
    (adj.ofNatIsoRight eR)
  exact ⟨preservesFiniteLimits_of_natIso e.symm,
    preservesFiniteColimits_of_natIso e.symm⟩

end AlgebraicGeometry.Scheme
