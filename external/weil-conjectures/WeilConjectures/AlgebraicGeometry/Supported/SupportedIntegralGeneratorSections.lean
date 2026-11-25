/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierProIntegralScalar

/-! # Constant sections of the supported integral generator

Source: the source normalization in the diagonal tower construction, step (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
attribute [local instance] AlgebraicGeometry.cartierEtaleAbSheafify
  WeilConjectures.sfAbSheafify AlgebraicGeometry.cartierEtaleModuleSheafify
  AlgebraicGeometry.cartierProModuleSheafify
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] comparisonUpperStar comparisonAdjunction cartierProIntegralGenerator
  cartierIntegralConstantComparisonIso cartierIntegralSourceIso cartierForgetComparison

private theorem etale_generator_constant (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (n : ℤ) :
    (Etale.ordinaryFiniteIntegralGenerator A X).hom.app
        (op (Scheme.Etale.mk (𝟙 X)))
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          (op (Scheme.Etale.mk (𝟙 X))) (ULift.up n)) =
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
          (op (Scheme.Etale.mk (𝟙 X))) (n : A) := by
  have h := Equiv.apply_symm_apply
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      (Scheme.Etale.isTerminalMkId X)).homEquiv
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))
        ((Etale.RawModuleScalarComparison.forget A X).obj
          (Etale.ordinaryFiniteConstant A X)))
    (AddCommGrpCat.ofHom
      ((((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
            (op (Scheme.Etale.mk (𝟙 X))))).hom).comp
        ((Int.castAddHom A).comp AddEquiv.ulift.toAddMonoidHom)))
  exact ConcreteCategory.congr_hom h (ULift.up n)

private abbrev constantGenerator (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (cartierForget A X).obj (geoCartierConstant A X) := by
  let Q := (cartierForget A X).obj (geoCartierConstant A X)
  let t : (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ Q.obj :=
    { app V := AddCommGrpCat.ofHom
        (((((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
          ((toSheafify (Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).app V)).hom)).comp
              ((Int.castAddHom A).comp AddEquiv.ulift.toAddMonoidHom))
      naturality := by
        intro V W f
        ext n
        have h := (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).naturality f
        exact ConcreteCategory.congr_hom h (n.down : A) }
  exact ⟨sheafifyLift (Scheme.ProEt.topology X) t Q.property⟩

private theorem constantGenerator_spec (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (V : X.ProEtᵒᵖ) (n : ℤ) :
    (constantGenerator A X).hom.app V
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V
            (ULift.up n)) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).app V (n : A) := by
  change ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
        (constantGenerator A X).hom).app V) (ULift.up n) = _
  unfold constantGenerator
  rw [toSheafify_sheafifyLift]
  rfl

private theorem integralComparison_constant (X : Scheme.{u}) (n : ℤ) :
    (cartierIntegralConstantComparisonIso X).hom.hom.app
        (op (Scheme.ProEt.mk (𝟙 X)))
      (((comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
        (Etale.supportedIntegralConstant X)).hom.app (op (Scheme.Etale.mk (𝟙 X)))
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
            (op (Scheme.Etale.mk (𝟙 X))) (ULift.up n))) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          (op (Scheme.ProEt.mk (𝟙 X))) (ULift.up n) := by
  let adj1 := (((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      (Scheme.Etale.isTerminalMkId X)).comp
        (comparisonAdjunction AddCommGrpCat.{u + 1} X)).ofNatIsoRight
      ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso
        AddCommGrpCat.{u + 1} X.smallEtaleTopology (Scheme.ProEt.topology X)
          (op (Scheme.Etale.mk (𝟙 X)))))
  let adj2 := constantSheafAdj (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
    (Scheme.ProEt.isTerminalMkId X)
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app adj1 adj2
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have he : (adj1.leftAdjointUniq adj2).hom.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
        (cartierIntegralConstantComparisonIso X).hom := by
    unfold cartierIntegralConstantComparisonIso
    rfl
  rw [he] at h
  dsimp only [adj1] at h
  erw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  dsimp only [Equiv.trans_apply] at h
  erw [constantSheafAdj_homEquiv_apply, Adjunction.homEquiv_unit] at h
  simp only [Functor.sheafPushforwardContinuousCompSheafSectionsObjIso] at h
  erw [Category.comp_id] at h
  dsimp only [adj2, constantSheafAdj] at h
  rw [Adjunction.comp_unit_app] at h
  simp only [constantPresheafAdj_unit_app, Category.id_comp] at h
  exact ConcreteCategory.congr_hom h (ULift.up n)

private theorem constantGenerator_comparison (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    (comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
        (Etale.supportedIntegralConstant X) ≫
      (comparisonLowerStar AddCommGrpCat.{u + 1} X).map
        (cartierIntegralConstantComparisonIso X).hom ≫
      (comparisonLowerStar AddCommGrpCat.{u + 1} X).map (constantGenerator A X) =
    Etale.ordinaryFiniteIntegralGenerator A X ≫
      (Etale.RawModuleScalarComparison.forget A X).map
        ((comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app
          (Etale.ordinaryFiniteConstant A X)) ≫
      (comparisonLowerStar AddCommGrpCat.{u + 1} X).map
        ((cartierForget A X).map
          (((comparisonUpperStarConstantSheafIso A X).app (ModuleCat.of A A)).hom)) := by
  apply ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (Scheme.Etale.isTerminalMkId X)).homEquiv _ _).injective
  erw [constantSheafAdj_homEquiv_apply, constantSheafAdj_homEquiv_apply]
  ext n
  obtain ⟨n⟩ := n
  change (constantGenerator A X).hom.app (op (Scheme.ProEt.mk (𝟙 X)))
      ((cartierIntegralConstantComparisonIso X).hom.hom.app _
        (((comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app _).hom.app _
          ((toSheafify X.smallEtaleTopology
            ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
              (op (Scheme.Etale.mk (𝟙 X))) (ULift.up n)))) = _
  erw [integralComparison_constant, constantGenerator_spec]
  change _ = (((comparisonUpperStarConstantSheafIso A X).app
      (ModuleCat.of A A)).hom).hom.app (op (Scheme.ProEt.mk (𝟙 X)))
    (((comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app
        (Etale.ordinaryFiniteConstant A X)).hom.app (op (Scheme.Etale.mk (𝟙 X)))
      ((Etale.ordinaryFiniteIntegralGenerator A X).hom.app
        (op (Scheme.Etale.mk (𝟙 X)))
          ((toSheafify X.smallEtaleTopology
            ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
              (op (Scheme.Etale.mk (𝟙 X))) (ULift.up n))))
  erw [etale_generator_constant, comparison_constant_generator]

private theorem integralSource_comparison_unit
    {X Z : Scheme.{u}} (i : X ⟶ Z) :
    (comparisonAdjunction AddCommGrpCat.{u + 1} Z).unit.app
        ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
          (Etale.supportedIntegralConstant X)) ≫
      (comparisonLowerStar AddCommGrpCat.{u + 1} Z).map
        (cartierIntegralSourceComparison i) =
    (Etale.lowerStar AddCommGrpCat.{u + 1} i).map
      ((comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
          (Etale.supportedIntegralConstant X) ≫
        (comparisonLowerStar AddCommGrpCat.{u + 1} X).map
          (cartierIntegralConstantComparisonIso X).hom) ≫
      (lowerStarCompComparisonLowerStarIso i AddCommGrpCat.{u + 1}).inv.app
        ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
  have hm := unit_mateEquiv_symm
    (comparisonAdjunction AddCommGrpCat.{u + 1} X)
    (comparisonAdjunction AddCommGrpCat.{u + 1} Z)
    (lowerStarCompComparisonLowerStarIso i AddCommGrpCat.{u + 1}).inv
    (Etale.supportedIntegralConstant X)
  change _ = (comparisonAdjunction AddCommGrpCat.{u + 1} Z).unit.app _ ≫
    (comparisonLowerStar AddCommGrpCat.{u + 1} Z).map
      ((lowerStarComparisonUpperStarBaseChange i AddCommGrpCat.{u + 1}).app
        (Etale.supportedIntegralConstant X)) at hm
  unfold cartierIntegralSourceComparison
  rw [Functor.map_comp, ← Category.assoc]
  erw [← hm]
  simp only [Functor.map_comp, Category.assoc]
  have hh := (lowerStarCompComparisonLowerStarIso i AddCommGrpCat.{u + 1}).inv.naturality
    (cartierIntegralConstantComparisonIso X).hom
  simp only [Functor.comp_map] at hh
  erw [← hh]

private theorem supportedGenerator_eq (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (i : X ⟶ Z) [IsClosedImmersion i] :
    cartierProIntegralGenerator A i =
      (lowerStar AddCommGrpCat.{u + 1} i).map (constantGenerator A X) := by
  apply (cancel_epi (cartierIntegralSourceIso i).hom).mp
  unfold cartierProIntegralGenerator
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let adj := comparisonAdjunction AddCommGrpCat.{u + 1} Z
  apply (adj.homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_naturality_right]
  unfold cartierForgetComparison
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  have hm := congrArg (Etale.RawModuleScalarComparison.forget A Z).map
    (source_comparison_unit A i)
  have hi := integralSource_comparison_unit i
  have hc := constantGenerator_comparison A X
  simp only [Functor.map_comp, Category.assoc] at hm hi hc ⊢
  change Etale.supportedIntegralGenerator A i ≫
      (Etale.RawModuleScalarComparison.forget A Z).map
        ((comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.app
          ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
            (Etale.ordinaryFiniteConstant A X)) ≫
          (comparisonLowerStar (ModuleCat.{u + 1} A) Z).map
            (geoCartierSourceComparison A i)) = _
  rw [← Functor.map_comp] at hm
  erw [hm]
  change _ = (comparisonAdjunction AddCommGrpCat.{u + 1} Z).unit.app
      ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
        (Etale.supportedIntegralConstant X)) ≫
    (comparisonLowerStar AddCommGrpCat.{u + 1} Z).map
      ((cartierIntegralSourceIso i).hom ≫
        (lowerStar AddCommGrpCat.{u + 1} i).map (constantGenerator A X))
  simp only [cartierIntegralSourceIso, asIso_hom]
  rw [Functor.map_comp]
  erw [reassoc_of% hi]
  have hn := (lowerStarCompComparisonLowerStarIso i AddCommGrpCat.{u + 1}).inv.naturality
    (constantGenerator A X)
  simp only [Functor.comp_map] at hn
  erw [← hn]
  have hc' := congrArg (Etale.lowerStar AddCommGrpCat.{u + 1} i).map hc
  simp only [Functor.map_comp] at hc'
  erw [reassoc_of% hc']
  rfl

/-- The supported integral generator sends a constant integer to its coefficient cast.

Source: diagonal tower system proof, step (3), source paragraph; the comparison
constant-generator calculation in the Cartier site-comparison proof.
(blueprint: new-sfb-supported-integral-generator-sections).

Proof: first evaluate the etale integral generator using the constant-sheaf/global-
sections adjunction. At the terminal object it is the coefficient integer cast,
by the defining hom equivalence, and naturality gives the same formula on every
etale object. Transpose the pro-etale generator equation through the comparison
adjunction. The unit equation of the supported-source base-change mate reduces
it to direct image of this etale constant-generator equation. The constant-sheaf
comparison is the unique comparison of the two constant/global-sections left
adjoints, so its unit equation carries the etale constant section to the identical
pro-etale constant section. The direct-image comparisons are the identity on
sections at the base-changed test object. Cancel the invertible supported integral
source comparison. This gives the asserted formula on every pro-etale test object.
No residue ring, reduction presentation, or completed coefficient is involved;
the formula also holds for zero rings and empty schemes. -/
theorem supported_integral_generator_sections (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (i : X ⟶ Z) [IsClosedImmersion i]
    (U : Z.ProEtᵒᵖ) (n : ℤ) :
    (cartierProIntegralGenerator A i).hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
            (op ((Scheme.proEtaleBaseChange i).obj U.unop)) (ULift.up n)) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          (op ((Scheme.proEtaleBaseChange i).obj U.unop)) (n : A) := by
  rw [supportedGenerator_eq]
  exact constantGenerator_spec A X _ n

end AlgebraicGeometry.ProEtale
