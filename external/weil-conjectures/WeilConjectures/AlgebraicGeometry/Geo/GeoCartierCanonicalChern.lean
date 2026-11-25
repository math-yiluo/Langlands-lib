/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalClass
import all WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import all WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import all WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import all WeilConjectures.CategoryTheory.DerivedSingleUnit
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarCoherence

/-! # The Cartier Chern equation under comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

private theorem ext_unit_transport {C E : Type*} [Category* C] [Category* E]
    [Abelian C] [Abelian E] [HasExt C] [HasExt E]
    (F : C ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y T : C} {P : E} (v : F.obj X ⟶ P) (u : X ⟶ Y)
    (b : F.obj Y ⟶ P) (κ : Ext Y T 2) (c : Ext P (F.obj T) 2)
    (hu : F.map u ≫ b = v)
    (hc : (Ext.mk₀ b).comp c (zero_add 2) = κ.mapExactFunctor F) :
    (Ext.mk₀ v).comp c (zero_add 2) =
      ((Ext.mk₀ u).comp κ (zero_add 2)).mapExactFunctor F := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ← hc,
    Ext.mk₀_comp_mk₀_assoc, hu]

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] comparisonUpperStar Ext.comp Ext.mk₀ Ext.mapExactFunctor
  geoCartierCanonicalClass Etale.geoCartierEtaleClass

private theorem comparison_constant_section (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (V : X.Etale) (a : A) :
    (((comparisonUpperStarConstantSheafIso A X).app (ModuleCat.of A A)).hom).hom.app
        ((Scheme.toProEt X).op.obj (op V))
      (((comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app
        (Etale.ordinaryFiniteConstant A X)).hom.app (op V)
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).app (op V) a)) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          ((Scheme.toProEt X).op.obj (op V)) a := by
  let e := ((comparisonUpperStarConstantSheafIso A X).app (ModuleCat.of A A)).hom
  let η := (comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app
    (Etale.ordinaryFiniteConstant A X)
  let adj1 := (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
      (Scheme.Etale.isTerminalMkId X)).comp
        (comparisonAdjunction (ModuleCat.{u + 1} A) X)).ofNatIsoRight
      ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso
        (ModuleCat.{u + 1} A) X.smallEtaleTopology (Scheme.ProEt.topology X)
          (op (Scheme.Etale.mk (𝟙 X)))))
  let adj2 := constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
    (Scheme.ProEt.isTerminalMkId X)
  have ht := ConcreteCategory.congr_hom
    (Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2 (ModuleCat.of A A)) a
  let f := (Scheme.Etale.isTerminalMkId X).from V
  have hn := NatTrans.naturality_apply
    (η ≫ (comparisonLowerStar (ModuleCat.{u + 1} A) X).map e).hom f.op
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
          (op (Scheme.Etale.mk (𝟙 X))) a)
  have he := ConcreteCategory.congr_hom
    ((toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).naturality f.op) a
  have hp := ConcreteCategory.congr_hom
    ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).naturality
        ((Scheme.toProEt X).map f).op) a
  simp only [Functor.const_obj_map, ModuleCat.comp_apply] at he hp
  change e.hom.app _ (η.hom.app _
    ((toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
        (op (Scheme.Etale.mk (𝟙 X))) a)) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          (op (Scheme.ProEt.mk (𝟙 X))) a at ht
  change e.hom.app _ (η.hom.app _
    ((sheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).map f.op
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
            (op (Scheme.Etale.mk (𝟙 X))) a))) =
      (sheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).map
          ((Scheme.toProEt X).map f).op
            (e.hom.app _ (η.hom.app _
              ((toSheafify X.smallEtaleTopology
                ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
                  (op (Scheme.Etale.mk (𝟙 X))) a))) at hn
  rw [← he] at hn
  erw [ht] at hn
  exact hn.trans hp.symm

private theorem pro_constant_section (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) (V : Z.ProEt) (a : A) :
    (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
      (ModuleCat.of A A)).hom.app (op V)
        ((toSheafify (Scheme.ProEt.topology Z)
          ((Functor.const Z.ProEtᵒᵖ).obj (ModuleCat.of A A))).app (op V) a) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          (op ((Scheme.proEtaleBaseChange i).obj V)) a := by
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology Z)
    (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const Z.ProEtᵒᵖ).obj (ModuleCat.of A A))
      ((lowerStar (ModuleCat.{u + 1} A) i).obj
        ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)))).apply_symm_apply
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange i).op
        (toSheafify (Scheme.ProEt.topology D)
          ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))))
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op V)) a

set_option maxRecDepth 2048 in
private theorem comparison_supported_unit (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).map (Etale.supportedConstantUnit A i) ≫
        geoCartierSourceComparison A i =
      ((comparisonUpperStarConstantSheafIso A Z).app (ModuleCat.of A A)).hom ≫
        Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
          (ModuleCat.of A A) := by
  unfold geoCartierSourceComparison geoCartierConstant Etale.ordinaryFiniteConstant
  apply ((comparisonAdjunction (ModuleCat.{u + 1} A) Z).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := (comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.naturality
    (Etale.supportedConstantUnit A i)
  simp only [Functor.id_map, Functor.comp_map] at hu
  rw [← reassoc_of% hu]
  rw [unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app_assoc]
  apply ((constantSheafAdj Z.smallEtaleTopology (ModuleCat.{u + 1} A)
    (Scheme.Etale.isTerminalMkId Z)).homEquiv _ _).injective
  rw [constantSheafAdj_homEquiv_apply, constantSheafAdj_homEquiv_apply]
  ext
  have hunit : Etale.supportedConstantUnit A i =
      Etale.constantSheafUnit i (ModuleCat.of A A) := by
    unfold Etale.supportedConstantUnit Etale.constantSheafUnit
    rw [Adjunction.homEquiv_apply]
    rfl
  have hi (G : Sheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} A)) :
      ((lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv.app G).hom.app
        (op (Scheme.Etale.mk (𝟙 Z))) = 𝟙 _ := by
    change G.obj.map (𝟙 _) = 𝟙 _
    exact G.obj.map_id _
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  erw [hi]
  let V := i.Etale.obj (Scheme.Etale.mk (𝟙 Z))
  change
    (((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom).hom.app
      ((Scheme.toProEt D).op.obj (op V))
      (((comparisonAdjunction (ModuleCat.{u + 1} A) D).unit.app
        (Etale.ordinaryFiniteConstant A D)).hom.app (op V)
        ((Etale.supportedConstantUnit A i).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
          ((toSheafify Z.smallEtaleTopology
            ((Functor.const Z.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
              (op (Scheme.Etale.mk (𝟙 Z))) (1 : A)))) =
    (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
      (ModuleCat.of A A)).hom.app (op (Scheme.ProEt.mk (𝟙 Z)))
      ((((comparisonUpperStarConstantSheafIso A Z).app (ModuleCat.of A A)).hom).hom.app
        (op (Scheme.ProEt.mk (𝟙 Z)))
        (((comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.app
          (Etale.ordinaryFiniteConstant A Z)).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
          ((toSheafify Z.smallEtaleTopology
            ((Functor.const Z.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
              (op (Scheme.Etale.mk (𝟙 Z))) (1 : A))))
  rw [hunit, Etale.constantSheafUnit_app_toSheafify]
  erw [comparison_constant_section A D V (1 : A),
    comparison_constant_section A Z (Scheme.Etale.mk (𝟙 Z)) (1 : A),
    pro_constant_section]
  rfl

/-- The normalized ordinary Cartier boundary satisfies the pro-etale Chern equation.
Source: blueprint sk-lem-geo-cartier.proof.md, paragraphs 1 and 5
(blueprint: lemma-cycle-class-cartier-divisor--1).
Proof: ordinary_supported_kummer supplies a boundary representative and its Kummer
Chern class. Uniqueness identifies that representative with geoCartierEtaleClass.
For a closed immersion, the exact direct-image comparison intertwines the degree-zero
constant unit with supportedDerivedUnit; its single-complex comparison intertwines
supportedExactDerivedMap with Ext.homEquiv. Thus the ordinary unit equation is the
Yoneda equation obtained by precomposition with the ordinary supported constant unit.
The comparison mate commutes with units, by the two adjunction triangle identities.
Apply exact comparison inverse image to this equation, identify the constants by
comparisonUpperStarConstantSheafIso, and cancel the invertible supported-source mate.
The resulting equation is precisely GeoCartierChernEquation, with the same ordinary
Chern witness and the same integral generator. No sign is changed: the pole frame is
the inverse Cartier equation, the frame of the dual ideal. For empty support both
sides are zero; for the zero coefficient ring all objects and equations are zero.
-/
theorem geoCartierCanonicalClass_chern (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :
    GeoCartierChernEquation A n hA i hI hZ
      (geoCartierCanonicalClass A n hn hA i hI hZ) := by
  let κ := Etale.geoCartierEtaleClass A n hn hA i hI hZ
  unfold GeoCartierChernEquation
  refine ⟨(Ext.mk₀ (Etale.supportedConstantUnit A i)).comp κ (zero_add 2), ?_, ?_⟩
  · rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.mk₀_comp_mk₀_assoc, Etale.coefficient_unit, ← Ext.mk₀_comp_mk₀_assoc]
    exact Etale.supported_kummer_chern_realization Z n A hA hZ i hI κ
      (Etale.geoCartierEtaleClass_spec A n hn hA i hI hZ).1
  · exact ext_unit_transport (comparisonUpperStar (ModuleCat.{u + 1} A) Z)
      _ (Etale.supportedConstantUnit A i) (geoCartierSourceComparison A i) κ
      (geoCartierCanonicalClass A n hn hA i hI hZ) (comparison_supported_unit A i)
      (geoCartierCanonicalClass_comparison A n hn hA i hI hZ)

end AlgebraicGeometry.ProEtale
