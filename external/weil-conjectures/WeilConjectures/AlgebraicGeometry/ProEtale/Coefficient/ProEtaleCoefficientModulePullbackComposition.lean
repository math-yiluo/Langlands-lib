/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact

/-! # Adjunction-normalized composition with independent coefficient universes

## References

* Stacks Project, Tag 03D8
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t r
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

private abbrev ringDirectImage {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max r (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)

private theorem constantSection_unit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) (W : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj A)).app W ≫
      (coefficientProEtaleDirectRingMap f A).hom.app W =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange f).op.obj W) := by
  have h := (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max r (t + 1)}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A)
    ((ringDirectImage.{t,r} f).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A))
    |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun t ↦ t.app W) h

private noncomputable def sheafComp {T Y X : Scheme.{t}} (a : Y ⟶ T) (b : X ⟶ Y) :
    ringDirectImage.{t,r} b ⋙
      ringDirectImage.{t,r} a ≅
        ringDirectImage.{t,r} (b ≫ a) :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).symm)
    CommRingCat.{max r (t + 1)} (ProEt.topology T) (ProEt.topology Y) (ProEt.topology X)

private theorem rho_comp {T Y X : Scheme.{t}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    coefficientProEtaleDirectRingMap a A ≫
      (ringDirectImage.{t,r} a).map
        (coefficientProEtaleDirectRingMap b A) ≫
          (sheafComp a b).hom.app
            ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A) =
            coefficientProEtaleDirectRingMap (b ≫ a) A := by
  apply (sheafificationAdjunction (ProEt.topology T) CommRingCat.{max r (t + 1)}).homEquiv _ _
    |>.injective
  apply NatTrans.ext
  funext W
  change _ ≫ _ ≫ _ ≫ _ = _ ≫ _
  rw [← Category.assoc, ← Category.assoc, constantSection_unit]
  change ((toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange a).op.obj W) ≫
      (coefficientProEtaleDirectRingMap b A).hom.app
        ((proEtaleBaseChange a).op.obj W)) ≫
      ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).hom.app
          W.unop).op =
    (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj A)).app W ≫
        (coefficientProEtaleDirectRingMap (b ≫ a) A).hom.app W
  rw [constantSection_unit,
    constantSection_unit]
  have hn := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).hom.app
        W.unop).op
  change 𝟙 _ ≫ _ = _ at hn
  exact hn.symm.trans (Category.id_comp _)

private def moduleRho {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).obj A) ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{max r (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
              ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A)) :=
  ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap f A).hom
    (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})⟩

private theorem moduleRho_comp {T Y X : Scheme.{t}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    letI := Functor.isContinuous_comp (proEtaleBaseChange a) (proEtaleBaseChange b)
      (ProEt.topology T) (ProEt.topology Y) (ProEt.topology X)
    moduleRho a A ≫
      ((proEtaleBaseChange a).sheafPushforwardContinuous RingCat.{max r (t + 1)}
        (ProEt.topology T) (ProEt.topology Y)).map (moduleRho b A) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a).hom
        RingCat.{max r (t + 1)} (ProEt.topology T) (ProEt.topology X)).app
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A)) =
              moduleRho (b ≫ a) A := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  simp only [moduleRho]
  exact congrArg
    (fun h ↦ (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)}).map (h.hom.app W))
    (rho_comp a b A)

private noncomputable def directComp {T Y X : Scheme.{t}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : CommRingCat.{max r (t + 1)}) :
    coefficientProEtaleModuleDirectImage b A ⋙ coefficientProEtaleModuleDirectImage a A ≅
      coefficientProEtaleModuleDirectImage (b ≫ a) A := by
  letI := Functor.isContinuous_comp (proEtaleBaseChange a) (proEtaleBaseChange b)
    (ProEt.topology T) (ProEt.topology Y) (ProEt.topology X)
  exact SheafOfModules.pushforwardComp (moduleRho a A) (moduleRho b A) ≪≫
    SheafOfModules.pushforwardNatIso _
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a) ≪≫
        SheafOfModules.pushforwardCongr (moduleRho_comp a b A)

end AlgebraicGeometry.Scheme
