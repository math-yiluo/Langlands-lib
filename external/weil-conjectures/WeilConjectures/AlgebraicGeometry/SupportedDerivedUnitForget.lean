/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystem
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.CategoryTheory.DerivedSingleUnitExact

/-!
# Integral evaluation of the exact derived closed unit

Source: blueprint lemma-cycle-class-cartier-divisor; Stacks 03PL and 0A45
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section
open MonoidalCategory
universe vC vD uC uD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{vC} C] [HasDerivedCategory.{vD} D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

variable [HasExt.{vC} C]

private theorem singleUnitCore_comp (adj : f ⊣ g) (X : C) (Y : D)
    (c : f.obj X ⟶ Y) (Z : C) (κ : Ext (g.obj Y) Z 2) :
    Ext.homEquiv.symm (Adjunction.derivedSingleUnit adj X Y c ≫
      AlgebraicGeometry.Etale.supportedExactDerivedMap g Y Z κ) =
    (Ext.mk₀ (adj.homEquiv X Y c)).comp κ (zero_add 2) := by
  apply Ext.homEquiv.injective
  rw [Ext.homEquiv.apply_symm_apply]
  change _ = ((Ext.mk₀ (adj.homEquiv X Y c)).comp κ (zero_add 2)).hom
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
  unfold AlgebraicGeometry.Etale.supportedExactDerivedMap
  simp only [Iso.app_hom]
  simpa only [Category.assoc] using congrArg (fun h => h ≫ κ.hom)
    (Adjunction.derivedSingleUnit_comp_comparison adj X Y c)

end

namespace AlgebraicGeometry.Etale

open Scheme

-- Match the instance proofs already stored in DerivedCategoryModule. Without this,
-- converting single objects unfolds the large sheafification construction in the kernel.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem derived_unit_class (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) F 2) :
    Ext.homEquiv.symm (supportedDerivedUnit A i ≫ supportedExactDerivedMap
      (lowerStar (ModuleCat.{u + 1} A) i) (ordinaryFiniteConstant A D) F κ) =
    (Ext.mk₀ (supportedConstantUnit A i)).comp κ (zero_add 2) := by
  unfold supportedDerivedUnit
  exact
    singleUnitCore_comp (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
      (ordinaryFiniteConstant A T) (ordinaryFiniteConstant A D)
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom.app
        (ModuleCat.of A A)) F κ

private def integralUnitAux {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    supportedIntegralConstant Y ⟶
      (lowerStar AddCommGrpCat.{u + 1} g).obj (supportedIntegralConstant Z) :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app _ ≫
    (lowerStar AddCommGrpCat.{u + 1} g).map
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
private theorem integral_unit_apply (V : Y.Etale) (m : ULift.{u + 1} ℤ) :
    (integralUnitAux g).hom.app (op V)
      ((CategoryTheory.toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op V) m) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) m := by
  let adjY := constantSheafAdj Y.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let adjZ := constantSheafAdj Z.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let e := Etale.lowerStarCompSheafSectionsTerminalIso (AddCommGrpCat.{u + 1}) g
  let adj := Etale.upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) g
  have key : (adjY.unit.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ ((sheafSections
    Y.smallEtaleTopology _).obj (op (⊤_ Y.Etale))).map
      (adj.unit.app ((constantSheaf Y.smallEtaleTopology _).obj (AddCommGrpCat.of (ULift.{u + 1}
        ℤ)))) ≫ e.hom.app _) ≫
      ((sheafSections Z.smallEtaleTopology _).obj (op (⊤_ Z.Etale))).map
        ((upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app (AddCommGrpCat.of
          (ULift.{u + 1} ℤ))) = adjZ.unit.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
    Adjunction.unit_leftAdjointUniq_hom_app ((adjY.comp adj).ofNatIsoRight e) adjZ
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have h := congr(($key).hom m)
  -- constant sections are compatible with restriction
  have hts {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) [HasWeakSheafify J
      (AddCommGrpCat.{u + 1})] {U W : C} (f : U ⟶ W) :
      (sheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).map f.op
        ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1}
          ℤ)))).app (op W) m) =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1}
        ℤ)))).app (op U) m :=
    (congr(($((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u +
      1} ℤ)))).naturality
      f.op)).hom m)).symm
  let θ := integralUnitAux g
  let F := MorphismProperty.Over.pullback @Etale ⊤ g
  let i := (PreservesTerminal.iso g.Etale)
  let G := (constantSheaf Z.smallEtaleTopology (AddCommGrpCat.{u + 1})).obj (AddCommGrpCat.of
    (ULift.{u + 1} ℤ))
  let x := (CategoryTheory.toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
    (op (⊤_ Y.Etale)) m
  have h₁ : G.obj.map i.op.symm.hom (θ.hom.app (op (⊤_ Y.Etale)) x) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op (⊤_ Z.Etale)) m :=
    (NatTrans.naturality_apply ((upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom
      i.op.symm.hom _).symm.trans h
  have hT : θ.hom.app (op (⊤_ Y.Etale)) x =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op (F.obj (⊤_ Y.Etale))) m := by
    have h₂ := congrArg (G.obj.map i.op.hom) h₁
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.id_apply] at h₂
    exact h₂.trans (hts Z.smallEtaleTopology i.hom)
  have hn := NatTrans.naturality_apply θ.hom (terminal.from V).op x
  rw [← hts Y.smallEtaleTopology (terminal.from V)]
  refine hn.trans ?_
  change G.obj.map (F.map (terminal.from V)).op (θ.hom.app (op (⊤_ Y.Etale)) x) = _
  rw [hT]
  exact hts Z.smallEtaleTopology _

private theorem generator_apply (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (V : T.Etale) (r : ULift.{u + 1} ℤ) :
    (ordinaryFiniteIntegralGenerator A T).hom.app (op V)
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op V) r) =
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (ModuleCat.of A A))).app (op V) (r.down : A) := by
  let terminal := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T
  let φ := AddCommGrpCat.ofHom
    ((((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
          (op (Scheme.Etale.mk (𝟙 T))))).hom).comp
      ((Int.castAddHom A).comp AddEquiv.ulift.toAddMonoidHom))
  have h := (constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminal).homEquiv (AddCommGrpCat.of (ULift.{u + 1} ℤ))
      ((moduleAbelianForget A T).obj (ordinaryFiniteConstant A T))
    |>.apply_symm_apply φ
  rw [constantSheafAdj_homEquiv_apply] at h
  have hT := ConcreteCategory.congr_hom h r
  change (ordinaryFiniteIntegralGenerator A T).hom.app (op (Scheme.Etale.mk (𝟙 T)))
    ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op (Scheme.Etale.mk (𝟙 T))) r) =
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (ModuleCat.of A A))).app (op (Scheme.Etale.mk (𝟙 T))) (r.down : A) at hT
  have hz := NatTrans.naturality_apply
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) (terminal.from V).op r
  have ha := NatTrans.naturality_apply
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (ModuleCat.of A A))) (terminal.from V).op (r.down : A)
  have hn := NatTrans.naturality_apply (ordinaryFiniteIntegralGenerator A T).hom
    (terminal.from V).op
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op (Scheme.Etale.mk (𝟙 T))) r)
  erw [hz.symm] at hn
  simp only [Functor.const_obj_map] at hn ha
  rw [hT] at hn
  exact hn.trans ha.symm

private theorem coefficient_unit (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    ordinaryFiniteIntegralGenerator A T ≫
      (moduleAbelianForget A T).map (supportedConstantUnit A i) =
    supportedIntegralUnit i ≫ supportedIntegralGenerator A i := by
  let terminal := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T
  apply ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminal).homEquiv _ _).injective
  rw [constantSheafAdj_homEquiv_apply, constantSheafAdj_homEquiv_apply]
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
  change ((moduleAbelianForget A T).map (supportedConstantUnit A i)).hom.app
    (op (Scheme.Etale.mk (𝟙 T)))
      ((ordinaryFiniteIntegralGenerator A T).hom.app (op (Scheme.Etale.mk (𝟙 T)))
        (supportedIntegralOne T)) =
    (supportedIntegralGenerator A i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
      ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
        (supportedIntegralOne T))
  have hmod : supportedConstantUnit A i = constantSheafUnit i (ModuleCat.of A A) := by
    unfold supportedConstantUnit constantSheafUnit
    rw [Adjunction.homEquiv_apply]
    rfl
  have hint : supportedIntegralUnit i = integralUnitAux i := by
    unfold supportedIntegralUnit integralUnitAux
    rw [Adjunction.homEquiv_apply]
    rfl
  rw [hint, hmod]
  change (constantSheafUnit i (ModuleCat.of A A)).hom.app (op (Scheme.Etale.mk (𝟙 T)))
    ((ordinaryFiniteIntegralGenerator A T).hom.app (op (Scheme.Etale.mk (𝟙 T)))
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op (Scheme.Etale.mk (𝟙 T)))
          (ULift.up 1))) = _
  rw [generator_apply A T, constantSheafUnit_app_toSheafify]
  change _ = (ordinaryFiniteIntegralGenerator A D).hom.app
    (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ i).obj
      (Scheme.Etale.mk (𝟙 T))))
    ((integralUnitAux i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op (Scheme.Etale.mk (𝟙 T)))
          (ULift.up 1)))
  rw [integral_unit_apply, generator_apply]

/-- Evaluation on the integral generator commutes with the derived closed unit
and its exact degree-zero direct-image comparison.
Source: Stacks 0A45, derived support-Hom unit normalization; blueprint
lemma-cycle-class-cartier-divisor, paragraph 4 (auxiliary; not a blueprint node).

Proof: exactness of closed direct image identifies its right-derived functor on
single objects with the single of direct image. The factorization formula for the
derived adjunction unit, and the single-complex comparison, identify the composite
of the derived unit and that comparison with the single of the underived unit.
Apply Ext.homEquiv and the functoriality of Ext under exact coefficient forgetting.
The integral coefficient generator is natural for the constant-sheaf unit: both
adjuncts send an integer r to its image r in A, on every etale object of the closed
support. Thus the resulting precomposition is the integral supported unit followed
by the supported coefficient generator. Yoneda associativity gives the equality.
This holds for the empty support and scheme, and no finiteness or flatness condition
on the coefficient ring is used. -/
theorem supported_derived_unit_forget (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) F 2) :
    (Ext.mk₀ (ordinaryFiniteIntegralGenerator A T)).comp
      ((Ext.homEquiv.symm (supportedDerivedUnit A i ≫ supportedExactDerivedMap
        (lowerStar (ModuleCat.{u + 1} A) i) (ordinaryFiniteConstant A D) F κ)).mapExactFunctor
          (moduleAbelianForget A T)) (zero_add 2) =
    (Ext.mk₀ (supportedIntegralUnit i)).comp
      ((Ext.mk₀ (supportedIntegralGenerator A i)).comp
        (κ.mapExactFunctor (moduleAbelianForget A T)) (zero_add 2))
      (zero_add 2) := by
  rw [derived_unit_class, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  simp only [Ext.mk₀_comp_mk₀_assoc, coefficient_unit]

end AlgebraicGeometry.Etale
