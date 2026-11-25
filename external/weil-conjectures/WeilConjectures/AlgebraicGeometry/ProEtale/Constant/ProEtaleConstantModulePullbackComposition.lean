/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackHomology
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteLocalConstancyPullback
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
/-!
# Composition of canonical constant-coefficient module restrictions

## References

* Stacks Project, Modules on Sites, Tag 03D8
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
private noncomputable def constAdj {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] : proEtaleConstantModulePullbackFunctor f A ⊣
      proEtaleConstantModuleDirectImage f A := by
  have := constantComparison_isIso f A
  let adj := proEtaleRingModuleAdjunction f (proEtaleConstantRing Y A)
    (proEtaleConstantRing X A) (asIso (proEtaleCoefficientInverseImageMap f A))
  change proEtaleConstantModulePullbackFunctor f A ⊣ _ at adj
  dsimp only [proEtaleRingModuleDirectImage] at adj
  rw [proEtaleConstantModulePullback_ring_direct] at adj
  exact adj
private noncomputable def sheafComp {T Y X : Scheme.{u}} (a : Y ⟶ T) (b : X ⟶ Y) :
    proEtaleSheafDirectImage b CommRingCat.{u + 1} ⋙
      proEtaleSheafDirectImage a CommRingCat.{u + 1} ≅
        proEtaleSheafDirectImage (b ≫ a) CommRingCat.{u + 1} :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).symm)
    CommRingCat.{u + 1} (ProEt.topology T) (ProEt.topology Y) (ProEt.topology X)

private theorem rho_comp {T Y X : Scheme.{u}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleCoefficientDirectImageMap a A ≫
      (proEtaleSheafDirectImage a CommRingCat.{u + 1}).map
        (proEtaleCoefficientDirectImageMap b A) ≫
          (sheafComp a b).hom.app (proEtaleConstantRing X A) =
            proEtaleCoefficientDirectImageMap (b ≫ a) A := by
  apply (sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv _ _
    |>.injective
  apply NatTrans.ext
  funext W
  change _ ≫ _ ≫ _ ≫ _ = _ ≫ _
  rw [← Category.assoc, ← Category.assoc, proEtaleConstantModulePullback_rho_unit]
  change ((toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
        ((proEtaleBaseChange a).op.obj W) ≫
      (proEtaleCoefficientDirectImageMap b A).hom.app
        ((proEtaleBaseChange a).op.obj W)) ≫
      (proEtaleConstantRing X A).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).hom.app
          W.unop).op =
    (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app W ≫
        (proEtaleCoefficientDirectImageMap (b ≫ a) A).hom.app W
  rw [proEtaleConstantModulePullback_rho_unit,
    proEtaleConstantModulePullback_rho_unit]
  have hn := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).naturality
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).hom.app
        W.unop).op
  change 𝟙 _ ≫ _ = _ at hn
  exact hn.symm.trans (Category.id_comp _)

private noncomputable def moduleRho {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] :
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing Y A) ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing X A)) :=
  ⟨Functor.whiskerRight (proEtaleCoefficientDirectImageMap f A).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private theorem moduleRho_comp {T Y X : Scheme.{u}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : Type u) [CommRing A] :
    letI := Functor.isContinuous_comp (proEtaleBaseChange a) (proEtaleBaseChange b)
      (ProEt.topology T) (ProEt.topology Y) (ProEt.topology X)
    moduleRho a A ≫
      ((proEtaleBaseChange a).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology T) (ProEt.topology Y)).map (moduleRho b A) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).hom
        RingCat.{u + 1} (ProEt.topology T) (ProEt.topology X)).app
          ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing X A)) = moduleRho (b ≫ a) A := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  exact congrArg
    (fun h ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map (h.hom.app W))
    (rho_comp a b A)

private noncomputable def directComp {T Y X : Scheme.{u}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleConstantModuleDirectImage b A ⋙ proEtaleConstantModuleDirectImage a A ≅
      proEtaleConstantModuleDirectImage (b ≫ a) A := by
  letI := Functor.isContinuous_comp (proEtaleBaseChange a) (proEtaleBaseChange b)
    (ProEt.topology T) (ProEt.topology Y) (ProEt.topology X)
  exact SheafOfModules.pushforwardComp (moduleRho a A) (moduleRho b A) ≪≫
    SheafOfModules.pushforwardNatIso _
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a) ≪≫
        SheafOfModules.pushforwardCongr (moduleRho_comp a b A)

private noncomputable def pullbackComp {T Y X : Scheme.{u}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleConstantModulePullbackFunctor (b ≫ a) A ≅
      proEtaleConstantModulePullbackFunctor a A ⋙
        proEtaleConstantModulePullbackFunctor b A :=
  ((constAdj (b ≫ a) A).ofNatIsoRight (directComp a b A).symm).leftAdjointUniq
    ((constAdj a A).comp (constAdj b A))
/-- The actual canonical constant-coefficient pullbacks compose up to isomorphism. -/
theorem proEtaleConstantModulePullback_comp {T Y X : Scheme.{u}}
    (a : Y ⟶ T) (b : X ⟶ Y) (A : Type u) [CommRing A] :
    Nonempty (proEtaleConstantModulePullbackFunctor (b ≫ a) A ≅
      proEtaleConstantModulePullbackFunctor a A ⋙
        proEtaleConstantModulePullbackFunctor b A) :=
  ⟨pullbackComp a b A⟩

end AlgebraicGeometry.Scheme
