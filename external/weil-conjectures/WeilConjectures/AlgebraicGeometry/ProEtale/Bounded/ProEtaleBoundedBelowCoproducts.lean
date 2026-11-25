/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleCohomologyCoproducts
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-!
# Pro-etale direct image and uniformly bounded-below coproducts

## References

* Stacks Project, Tag 09A3, relative rational-algebra module version
-/

@[expose] public section

set_option linter.privateModule false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

-- Match the site and section universes before applying the small-site theorem.
private noncomputable def moduleModelEquiv (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ≌
      SheafOfModules.{u + 1}
        (((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (proEtaleModelTopology T) (ProEt.topology T)).obj R) := by
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := T.ProEt)).symm.functor.IsContinuous
      (proEtaleModelTopology T) (ProEt.topology T) :=
    inferInstanceAs ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).IsContinuous _ _)
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := T.ProEt)).symm.inverse.IsContinuous
      (ProEt.topology T) (proEtaleModelTopology T) :=
    proEtaleModelUp_isContinuous T
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := T.ProEt)).symm
    (𝟙 _) (𝟙 _) (by
      ext V x
      change (R.obj.map (𝟙 V)) x = x
      simp) (by
      ext V x
      change (R.obj.map (𝟙 (Opposite.op (ULift.down V.unop)))) x = x
      simp)

private theorem moduleEnoughInjectives (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    EnoughInjectives (proEtaleRingModules T R) := by
  let R' := (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let S := ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology T) (ProEt.topology T)).obj R'
  have : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1} S) :=
    SheafOfModules.isGrothendieckAbelian S
  exact EnoughInjectives.of_equivalence (moduleModelEquiv T R').functor

-- A bounded-below complex of acyclic objects computes the unbounded derived functor.
private theorem unit_of_acyclic {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) (N : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ n, F.rightAcyclic (K.X n)) :
    IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)) := by
  obtain ⟨J, f, hf, hJ, hJN⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N
  have : QuasiIso f := hf
  have : J.IsStrictlyGE N := hJN
  have : ∀ n, Injective (J.X n) := hJ
  have : J.IsKInjective := CochainComplex.isKInjective_of_injective J N
  have : QuasiIso ((F.mapHomologicalComplex _).map f) :=
    F.quasiIso_map_of_rightAcyclic f N hK (fun n ↦ F.rightAcyclic_of_injective _)
  have hn := F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient C (.up ℤ)).map f)
  dsimp only [Functor.comp_map] at hn
  have hi : IsIso (F.rightDerivedFunctor.map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f))) := by
    have : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (.up ℤ)).map f)) := by
      change IsIso ((HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh).map f)
      exact NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) f |>.2 inferInstance
    infer_instance
  have hi' : IsIso ((F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient C (.up ℤ)).map f)) := by
    change IsIso ((HomotopyCategory.quotient D (.up ℤ) ⋙ DerivedCategory.Qh).map
      ((F.mapHomologicalComplex _).map f))
    exact NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso D) _ |>.2 inferInstance
  dsimp only [Functor.comp_map] at hi'
  have : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
      F.rightDerivedFunctor.map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f))) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctor.map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f)))

-- Transport a coproduct through the natural comparison from termwise direct image.
private theorem uniformCoproduct
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) [F.Additive] (I : Type (u + 1))
    [HasCoproducts.{u + 1} C] [HasCoproducts.{u + 1} D]
    [PreservesColimitsOfShape (Discrete I) F]
    (E : I → CochainComplex C ℤ)
    [∀ i, (E i).IsKInjective]
    (hunit : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj (∐ E)))) :
    PreservesColimit (Discrete.functor (fun i ↦ DerivedCategory.Q.obj (E i)))
      F.rightDerivedFunctor := by
  let v (K : CochainComplex C ℤ) : DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
    (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
        F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K)
  have nat {K L : CochainComplex C ℤ} (f : K ⟶ L) :
      DerivedCategory.Q.map ((F.mapHomologicalComplex _).map f) ≫ v L =
        v K ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map f) := by
    have h := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient C (.up ℤ)).map f)
    simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at h
    simp only [v, DerivedCategory.quotientCompQhIso_inv_naturality_assoc, Category.assoc]
    rw [reassoc_of% h, ← Functor.map_comp, ← Functor.map_comp,
      DerivedCategory.quotientCompQhIso_hom_naturality]
  have hu (i : I) : IsIso (v (E i)) := by dsimp only [v]; infer_instance
  have huP : IsIso (v (∐ E)) := by dsimp only [v]; infer_instance
  have hFc : IsColimit (Cofan.mk
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj (∐ E)))
      fun i ↦ DerivedCategory.Q.map ((F.mapHomologicalComplex _).map (Sigma.ι E i))) :=
    DerivedCategory.isColimitCofanMkQObj
      ((isColimitMapCoconeCofanMkEquiv (F.mapHomologicalComplex (.up ℤ)) E (Sigma.ι E)).1
        (isColimitOfPreserves (F.mapHomologicalComplex (.up ℤ)) (coproductIsCoproduct E)))
  refine preservesColimit_of_preserves_colimit_cocone
    (DerivedCategory.isColimitCofanMkQObj (coproductIsCoproduct E))
    ((isColimitMapCoconeCofanMkEquiv _ _ _).2 ?_)
  refine (IsColimit.equivOfNatIsoOfIso (Discrete.natIso fun i ↦ asIso (v (E i.as))) _ _
    (Cocone.ext (asIso (v (∐ E))) fun i ↦ ?_)) hFc
  dsimp
  rw [Category.assoc, nat]
  simp

end AlgebraicGeometry.Scheme
