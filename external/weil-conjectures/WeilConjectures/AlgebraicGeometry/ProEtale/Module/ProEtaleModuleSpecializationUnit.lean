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
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSpecializationRestrictionSections
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
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

/-! Module inverse-image units on weakly contractible specialization neighbourhoods.

## References

* Stacks Project, Tags 09AC and 03D2
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private noncomputable def modelSheafEquivalence (X : Scheme.{u}) :
    Sheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1} ≌
      Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)
@[irreducible] private noncomputable def modelAbelianAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (modelSheafEquivalence Y).functor ⋙ proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ⋙
      (modelSheafEquivalence X).inverse ⊣
        (proEtaleModelBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
  (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).restrictFullyFaithful
    (modelSheafEquivalence Y).fullyFaithfulFunctor
    (modelSheafEquivalence X).fullyFaithfulFunctor
    (Iso.refl _) (Iso.refl _)
private theorem modelAbelianAdjunction_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}) :
    (modelAbelianAdjunction f).unit.app ((modelSheafEquivalence Y).inverse.obj R) =
      ⟨CategoryTheory.Functor.whiskerLeft AsSmall.down.op
        ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app R).hom⟩ := by
  apply (modelSheafEquivalence Y).functor.map_injective
  rw [modelAbelianAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app]
  rfl

private theorem model_abelian_unit_bijective {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (V : X.ProEt) [IsAffine V.left]
    (hweak : ∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes x ((pullback.fst V.hom i) z))
    (M : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    Function.Bijective
      (((sheafAdjunctionContinuous (proEtaleModelBaseChange i) AddCommGrpCat.{u + 1}
        (proEtaleModelTopology X) (proEtaleModelTopology Z)).unit.app
        ((modelSheafEquivalence X).inverse.obj M)).hom.app (op (AsSmall.up.obj V))) := by
  let a := modelAbelianAdjunction i
  let b := sheafAdjunctionContinuous (proEtaleModelBaseChange i) AddCommGrpCat.{u + 1}
    (proEtaleModelTopology X) (proEtaleModelTopology Z)
  let N := (modelSheafEquivalence X).inverse.obj M
  let E := (sheafToPresheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1}) ⋙
    (CategoryTheory.evaluation _ _).obj (op (AsSmall.up.obj V))
  have : IsIso (E.map (a.unit.app N)) := by
    have := isIso_proEtaleUnit_sections_of_specialization i V hweak hspec
    have : IsIso ((((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit.app M).hom).app
        (op V)) := inferInstanceAs
      (IsIso (((Functor.whiskerRight
        (proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit
        ((sheafSections (ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op V))).app M)))
    change IsIso (((modelAbelianAdjunction i).unit.app N).hom.app (op (AsSmall.up.obj V)))
    rw [modelAbelianAdjunction_unit]
    exact this
  have h := congrArg E.map (Adjunction.unit_leftAdjointUniq_hom_app a b N)
  rw [E.map_comp] at h
  have : IsIso (E.map (b.unit.app N)) := by
    rw [← h]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (E.map (b.unit.app N))

private theorem model_module_unit_bijective {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (V : X.ProEt) [IsAffine V.left]
    (hweak : ∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes x ((pullback.fst V.hom i) z))
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    Function.Bijective
      (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit i R)).unit.app
        ((proEtaleModuleToModel _).obj M)).val.app (op (AsSmall.up.obj V))) := by
  let : (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : Z.ProEt ⥤ proEtaleSiteModel Z).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Z.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange i) := by
    change PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt) ⋙ proEtaleBaseChange i ⋙ AsSmall.up)
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange i) := flat_of_preservesFiniteLimits _
  obtain ⟨p, hp⟩ := proEtaleModelRingPresentation i R
  obtain ⟨e, he⟩ := SheafOfModules.inverseImage_underlying_unit_of_ring_presentation
    (proEtaleModelRingUnit i R) p (by ext U r; exact hp U r)
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let N := (proEtaleModuleToModel A).obj M
  let E := (sheafToPresheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1}) ⋙
    (CategoryTheory.evaluation _ _).obj (op (AsSmall.up.obj V))
  have h := congrArg E.map (he N)
  rw [E.map_comp] at h
  have hb := model_abelian_unit_bijective i V hweak hspec ((SheafOfModules.toSheaf A).obj M)
  have : IsIso (E.map ((sheafAdjunctionContinuous (proEtaleModelBaseChange i)
      AddCommGrpCat.{u + 1} (proEtaleModelTopology X) (proEtaleModelTopology Z)).unit.app
      ((SheafOfModules.toSheaf _).obj N))) :=
    by
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      exact hb
  have : IsIso (E.map ((SheafOfModules.toSheaf _).map
      ((SheafOfModules.pullbackPushforwardAdjunction
        (proEtaleModelRingUnit i R)).unit.app N))) := by
    have : IsIso (E.map ((SheafOfModules.toSheaf _).map
        ((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit i R)).unit.app N)) ≫
        E.map ((proEtaleModelBaseChange i).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (proEtaleModelTopology X) (proEtaleModelTopology Z) |>.map
            (e.hom.app N))) := h ▸ inferInstance
    exact IsIso.of_isIso_comp_right _ (E.map
      ((proEtaleModelBaseChange i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (proEtaleModelTopology X) (proEtaleModelTopology Z) |>.map (e.hom.app N)))
  exact ConcreteCategory.bijective_of_isIso (E.map ((SheafOfModules.toSheaf _).map
    ((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit i R)).unit.app N)))
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

/-- The module inverse-image unit is bijective on specialization-neighbourhood sections. -/
theorem proEtale_module_unit_bijective_of_specialization
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
    (hweak : ∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes x ((pullback.fst V.hom i) z))
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (ai : proEtaleModuleInverseImage i A ⊣
      (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩))
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) :
    Function.Bijective ((ai.unit.app M).val.app (op V)) := by
  let R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
  let S := (sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)
  let eX := proEtaleModuleModelEquivalence X R
  let eZ := proEtaleModuleModelEquivalence Z S
  let am := SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit i A)
  let adj := eX.symm.toAdjunction.comp (am.comp eZ.toAdjunction)
  change proEtaleModuleInverseImage i A ⊣ _ at adj
  let c : ((eZ.inverse ⋙ SheafOfModules.pushforward (proEtaleModelRingUnit i A)) ⋙
      eX.symm.inverse) ≅ SheafOfModules.pushforward.{u + 1}
        (F := proEtaleBaseChange i) (J := ProEt.topology X) (K := ProEt.topology Z)
        (S := R) (R := S)
        ⟨Functor.whiskerRight ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ := NatIso.ofComponents (fun N ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by intros; rfl))) (by
        intro N P a
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro W
        rfl)
  let ac := adj.ofNatIsoRight c
  let E := SheafOfModules.evaluation R (op V)
  have hm := model_module_unit_bijective i V hweak hspec A M
  have : IsIso (E.map (eX.functor.map (am.unit.app (eX.inverse.obj M)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hm
  have : IsIso (E.map (adj.unit.app M)) := by
    have h₁ : IsIso (E.map (eX.symm.toAdjunction.unit.app M)) := inferInstance
    have h₂ : IsIso (E.map (eX.symm.inverse.map
        (am.unit.app (eX.symm.functor.obj M)))) := by
      exact ‹IsIso (E.map (eX.functor.map (am.unit.app (eX.inverse.obj M))))›
    have h₃ : IsIso (E.map (eX.symm.inverse.map
        ((SheafOfModules.pushforward (proEtaleModelRingUnit i A)).map
          (eZ.toAdjunction.unit.app
            ((SheafOfModules.pullback (proEtaleModelRingUnit i A)).obj
              (eX.symm.functor.obj M)))))) := inferInstance
    change IsIso (E.map ((eX.symm.toAdjunction.comp (am.comp eZ.toAdjunction)).unit.app M))
    rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
    let f := eX.symm.toAdjunction.unit.app M
    let g := eX.symm.inverse.map (am.unit.app (eX.symm.functor.obj M))
    let h := eX.symm.inverse.map
      ((SheafOfModules.pushforward (proEtaleModelRingUnit i A)).map
        (eZ.toAdjunction.unit.app
          ((SheafOfModules.pullback (proEtaleModelRingUnit i A)).obj (eX.symm.functor.obj M))))
    have hm : E.map (f ≫ g ≫ h) = E.map f ≫ E.map g ≫ E.map h :=
      (E.map_comp f (g ≫ h)).trans (congrArg (fun t ↦ E.map f ≫ t) (E.map_comp g h))
    erw [eX.symm.inverse.map_comp]
    change IsIso (E.map (f ≫ g ≫ h))
    rw [hm]
    exact @IsIso.comp_isIso _ _ _ _ _ (E.map f) (E.map g ≫ E.map h) h₁
      (@IsIso.comp_isIso _ _ _ _ _ (E.map g) (E.map h) h₂ h₃)
  have : IsIso (E.map (ac.unit.app M)) := by
    change IsIso (E.map (adj.unit.app M ≫ c.hom.app _))
    rw [E.map_comp]
    infer_instance
  have h := congrArg E.map (Adjunction.unit_leftAdjointUniq_hom_app ac ai M)
  rw [E.map_comp] at h
  have : IsIso (E.map (ai.unit.app M)) := by
    rw [← h]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (E.map (ai.unit.app M))
end AlgebraicGeometry.Scheme
