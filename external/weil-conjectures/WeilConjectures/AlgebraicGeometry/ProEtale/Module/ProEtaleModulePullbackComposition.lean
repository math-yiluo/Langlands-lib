/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations

/-!
# Composition of pro-etale module inverse images with constant coefficients

## References

* Tag 03D8
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem constantSection_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] (W : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app W ≫
      (proEtaleCoefficientDirectImageMap f A).hom.app W =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
        ((proEtaleBaseChange f).op.obj W) := by
  have h := (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A))
    |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))))
  exact congrArg (fun t ↦ t.app W) h

private theorem constantRing_direct
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    [IsIso (proEtaleCoefficientInverseImageMap f A)] :
    proEtaleRingDirectImageMap f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (asIso (proEtaleCoefficientInverseImageMap f A)) =
        proEtaleCoefficientDirectImageMap f A := by
  exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    |>.apply_symm_apply (proEtaleCoefficientDirectImageMap f A)

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
  rw [← Category.assoc, ← Category.assoc, constantSection_unit]
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
  rw [constantSection_unit,
    constantSection_unit]
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
  ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)).hom
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
  simp only [moduleRho, proEtaleConstantRingComparison, constantRing_direct]
  exact congrArg
    (fun h ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map (h.hom.app W))
    (rho_comp a b A)

private noncomputable def directComp {T Y X : Scheme.{u}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingPushforward A b ⋙ proEtaleConstantRingPushforward A a ≅
      proEtaleConstantRingPushforward A (b ≫ a) := by
  letI := Functor.isContinuous_comp (proEtaleBaseChange a) (proEtaleBaseChange b)
    (ProEt.topology T) (ProEt.topology Y) (ProEt.topology X)
  exact SheafOfModules.pushforwardComp (moduleRho a A) (moduleRho b A) ≪≫
    SheafOfModules.pushforwardNatIso _
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b a) ≪≫
        SheafOfModules.pushforwardCongr (moduleRho_comp a b A)

/--
For composable morphisms of schemes and any commutative constant coefficient ring, the
module inverse image for the composite is canonically isomorphic to the successive inverse
images, compatibly with the identification of direct images and the module adjunctions.
-/
theorem proEtaleConstantRingModulePullbackComposition
    {X Y Z : Scheme.{u}} (g : Z ⟶ X) (f : X ⟶ Y)
    (Λ : Type u) [CommRing Λ] :
    ∃ (a : proEtaleConstantRingPullback Λ (g ≫ f) ≅
        proEtaleConstantRingPullback Λ f ⋙ proEtaleConstantRingPullback Λ g),
      ∃ (d : proEtaleConstantRingPushforward Λ g ⋙
          proEtaleConstantRingPushforward Λ f ≅
          proEtaleConstantRingPushforward Λ (g ≫ f)),
        (∀ (N : proEtaleRingModules Z (proEtaleConstantRing Z Λ))
            (U : Y.ProEt)
            (m : ((proEtaleConstantRingPushforward Λ g ⋙
              proEtaleConstantRingPushforward Λ f).obj N).val.obj (Opposite.op U)),
          (d.hom.app N).val.app (Opposite.op U) m =
            N.val.map ((MorphismProperty.Over.pullbackComp g f).hom.app U).op m) ∧
        conjugateIsoEquiv
            ((proEtaleConstantRingAdjunction Λ f).comp
              (proEtaleConstantRingAdjunction Λ g))
            (proEtaleConstantRingAdjunction Λ (g ≫ f)) a = d := by
  let d := directComp f g Λ
  let e := conjugateIsoEquiv
    ((proEtaleConstantRingAdjunction Λ f).comp (proEtaleConstantRingAdjunction Λ g))
    (proEtaleConstantRingAdjunction Λ (g ≫ f))
  refine ⟨e.symm d, d, ?_, e.apply_symm_apply d⟩
  intro N U m
  dsimp only [d, directComp]
  simp only [Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app]
  rfl

end AlgebraicGeometry.Scheme
