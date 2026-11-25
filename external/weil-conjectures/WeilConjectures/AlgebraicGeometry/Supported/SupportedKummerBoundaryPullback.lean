/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import WeilConjectures.AlgebraicGeometry.Cartier.CartierPoleBoundaryPullback
import WeilConjectures.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Data.ZMod.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarSource
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import WeilConjectures.CategoryTheory.FlatScalarUnit
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Stalk
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.ScalarUniversalDerivedUnit
import WeilConjectures.AlgebraicGeometry.SupportedIntegralResidueSequence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ScalarUnitExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import all WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import all WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import all WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import all WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# Cartier pullback of the supported Kummer boundary

Source: blueprint lemma-cycle-class-cartier-divisor; Stacks 03PL and 0A45
(blueprint: lem-asd-supported-kummer-boundary-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u uC uB uD uE vC vB vD vE wC wB wD wE
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- Match the stored instances of the boundary and scalar interfaces.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

section ExactSquare
variable {C : Type uC} {B : Type uB} {D : Type uD} {E : Type uE}
  [Category.{vC} C] [Category.{vB} B] [Category.{vD} D] [Category.{vE} E]
  [Abelian C] [Abelian B] [Abelian D] [Abelian E]
  [HasExt.{wC} C] [HasExt.{wB} B] [HasExt.{wD} D] [HasExt.{wE} E]
  (F : C ⥤ D) (G : B ⥤ E) (U : C ⥤ B) (V : D ⥤ E)
  [F.Additive] [G.Additive] [U.Additive] [V.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exactSquare (τ : U ⋙ G ≅ F ⋙ V) {P Q : C} {n : ℕ}
    (c : Ext.{wC} P Q n) :
    ((c.mapExactFunctor U).mapExactFunctor G).comp (Ext.mk₀ (τ.hom.app Q)) (add_zero n) =
      (Ext.mk₀ (τ.hom.app P)).comp
        ((c.mapExactFunctor F).mapExactFunctor V) (zero_add n) := by
  have hc := Ext.mapExactFunctor_comp_mk₀_eq_sheaf U G (U ⋙ G) (Iso.refl _) c
  simp only [Iso.refl_hom, NatTrans.id_app, Ext.comp_mk₀_id, Ext.mk₀_id_comp] at hc
  rw [← hc]
  exact Ext.mapExactFunctor_comp_mk₀_eq_sheaf F V (U ⋙ G) τ c

private theorem scalar_adjunct_pullback (τ : U ⋙ G ≅ F ⋙ V)
    {P Q : C} {X : B} {X' : E} {P' Q' : D}
    (η : X ⟶ U.obj P) (η' : X' ⟶ V.obj P')
    (s : G.obj X ≅ X') (a : F.obj P ≅ P') (l : F.obj Q ⟶ Q')
    (hη : s.hom ≫ η' = G.map η ≫ τ.hom.app P ≫ V.map a.hom)
    (c : Ext.{wC} P Q 2) :
    (Ext.mk₀ η').comp
        (((Ext.mk₀ a.inv).comp
          ((c.mapExactFunctor F).comp (Ext.mk₀ l) (add_zero 2))
          (zero_add 2)).mapExactFunctor V) (zero_add 2) =
      (Ext.mk₀ s.inv).comp
        ((((Ext.mk₀ η).comp (c.mapExactFunctor U) (zero_add 2)).mapExactFunctor G).comp
          (Ext.mk₀ (τ.hom.app Q ≫ V.map l)) (add_zero 2)) (zero_add 2) := by
  have hηinv : η' ≫ V.map a.inv = s.inv ≫ G.map η ≫ τ.hom.app P := by
    have h := congrArg (fun f ↦ s.inv ≫ f ≫ V.map a.inv) hη
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← V.map_comp,
      Iso.hom_inv_id, V.map_id] at h
    erw [Category.comp_id] at h
    exact h
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc]
  rw [hηinv]
  simp only [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]
  rw [← Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ (τ.hom.app P)),
    ← exactSquare F G U V τ c]
  simp only [Ext.comp_assoc_of_third_deg_zero]

end ExactSquare

private theorem iso_square_forward {C : Type uC} [Category.{vC} C]
    {X Y Z W : C} (e : X ≅ Y) (f : Z ≅ W) (a : Y ⟶ W) (b : X ⟶ Z)
    (h : a ≫ f.inv = e.inv ≫ b) : e.hom ≫ a = b ≫ f.hom := by
  apply (cancel_mono f.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  simp only [Iso.hom_inv_id_assoc]

private theorem forget_lowerStar_map (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (a : F ⟶ G) :
    (moduleAbelianForget A Y).map ((lowerStar (ModuleCat.{u + 1} A) f).map a) =
      (lowerStar AddCommGrpCat.{u + 1} f).map ((moduleAbelianForget A X).map a) := by
  rfl

private theorem integralGenerator_pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (v : X ⟶ Y) :
    (upperStar AddCommGrpCat.{u + 1} v).map (ordinaryFiniteIntegralGenerator A Y) ≫
        (moduleAbelianUpperStarComparison A v).app _ ≫
        (moduleAbelianForget A X).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
            (ModuleCat.of A A)).hom =
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} v).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom ≫
        ordinaryFiniteIntegralGenerator A X := by
  apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  dsimp only [moduleAbelianUpperStarComparison]
  erw [Equiv.apply_symm_apply]
  simpa only [supportedConstantUnit, supportedIntegralUnit, supportedIntegralGenerator,
    Adjunction.homEquiv_unit, Functor.map_comp, forget_lowerStar_map, Category.assoc,
    RawModuleScalarComparison.forget] using coefficient_unit A v

private theorem moduleExchange_forward (A : Type (u + 1)) [CommRing A]
    {D D' T T' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : CommSq w i' i v)
    (P : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (moduleAbelianUpperStarIso A v).hom.app
        ((lowerStar (ModuleCat.{u + 1} A) i).obj P) ≫
      (moduleAbelianForget A T').map ((baseChangeMap (ModuleCat.{u + 1} A) sq).app P) =
    (baseChangeMap AddCommGrpCat.{u + 1} sq).app ((moduleAbelianForget A D).obj P) ≫
      (lowerStar AddCommGrpCat.{u + 1} i').map
        ((moduleAbelianUpperStarIso A w).hom.app P) := by
  have hex := moduleAbelianUnderivedExchange_compatibility A sq P
  simp only [moduleAbelianLowerStarIso, Iso.refl_hom, NatTrans.id_app] at hex
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp] at hex
  exact iso_square_forward ((moduleAbelianUpperStarIso A v).app _)
    ((lowerStar AddCommGrpCat.{u + 1} i').mapIso
      ((moduleAbelianUpperStarIso A w).app P)) _ _ hex

private theorem moduleUpperStarIso_hom (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (v : X ⟶ Y)
    (P : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (moduleAbelianUpperStarIso A v).hom.app P =
      (moduleAbelianUpperStarComparison A v).app P := by
  rfl

private theorem generator_exchange (A : Type (u + 1)) [CommRing A]
    {D D' T T' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : CommSq w i' i v)
    {P : Sheaf D.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {Q : Sheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {P' : Sheaf D'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {Q' : Sheaf D'.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (g : P ⟶ (moduleAbelianForget A D).obj Q)
    (g' : P' ⟶ (moduleAbelianForget A D').obj Q')
    (a : (upperStar (ModuleCat.{u + 1} A) w).obj Q ⟶ Q')
    (b : (upperStar AddCommGrpCat.{u + 1} w).obj P ⟶ P')
    (hg : (upperStar AddCommGrpCat.{u + 1} w).map g ≫
        (moduleAbelianUpperStarIso A w).hom.app Q ≫
        (moduleAbelianForget A D').map a = b ≫ g') :
    (upperStar AddCommGrpCat.{u + 1} v).map
        ((lowerStar AddCommGrpCat.{u + 1} i).map g) ≫
      (moduleAbelianUpperStarIso A v).hom.app
        ((lowerStar (ModuleCat.{u + 1} A) i).obj Q) ≫
      (moduleAbelianForget A T').map
        ((baseChangeMap (ModuleCat.{u + 1} A) sq).app Q ≫
          (lowerStar (ModuleCat.{u + 1} A) i').map a) =
    ((baseChangeMap AddCommGrpCat.{u + 1} sq).app P ≫
        (lowerStar AddCommGrpCat.{u + 1} i').map b) ≫
      (lowerStar AddCommGrpCat.{u + 1} i').map g' := by
  have hf := moduleExchange_forward A i i' v w sq Q
  have hn := (baseChangeMap AddCommGrpCat.{u + 1} sq).naturality g
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, forget_lowerStar_map]
  rw [reassoc_of% hf, reassoc_of% hn]
  simp only [Category.assoc, ← Functor.map_comp, hg]

private theorem supportedGenerator_pullback (A : Type (u + 1)) [CommRing A]
    {D D' T T' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : CommSq w i' i v) :
    (upperStar AddCommGrpCat.{u + 1} v).map (supportedIntegralGenerator A i) ≫
        (moduleAbelianUpperStarComparison A v).app _ ≫
        (moduleAbelianForget A T').map (supportedConstantExchange A i i' v w sq) =
      relativeExtensionExchange i i' v w sq ≫ supportedIntegralGenerator A i' := by
  have hg := integralGenerator_pullback A w
  have h := generator_exchange A i i' v w sq
    (ordinaryFiniteIntegralGenerator A D) (ordinaryFiniteIntegralGenerator A D')
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) w).app
      (ModuleCat.of A A)).hom
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} w).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom (by
        simpa only [moduleUpperStarIso_hom] using hg)
  simpa only [moduleUpperStarIso_hom, supportedIntegralGenerator,
    supportedConstantExchange, relativeExtensionExchange] using h

private theorem rootMap_pullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (v : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (upperStar AddCommGrpCat.{u + 1} v).map (ordinaryFiniteRootMap A N hA Y) ≫
        (moduleAbelianUpperStarComparison A v).app _ ≫
        (moduleAbelianForget A X).map (t.line v hY).hom =
      (t.roots v hY).hom ≫ ordinaryFiniteRootMap A N hA X := by
  apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  dsimp only [moduleAbelianUpperStarComparison]
  erw [Equiv.apply_symm_apply]
  ext W z
  exact t.line_normalization v hY W 1 z

private theorem kummerUnit_pullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (v : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
    (hX : IsUnit (N : Γ(X, ⊤))) :
    (Ext.mk₀ (Scheme.upperStarGmSheafToGmSheaf v)).comp
        (ProEtale.cartierEtaleKummerUnit A N hA X hX) (zero_add 1) =
      ((ProEtale.cartierEtaleKummerUnit A N hA Y hY).mapExactFunctor
        (upperStar AddCommGrpCat.{u + 1} v)).comp
        (Ext.mk₀ ((moduleAbelianUpperStarComparison A v).app _ ≫
          (moduleAbelianForget A X).map (t.line v hY).hom)) (add_zero 1) := by
  let F := upperStar AddCommGrpCat.{u + 1} v
  let b := Scheme.upperStarGmSheafToGmSheaf v
  let ψ : (Y.kummerSequence N).map F ⟶ X.kummerSequence N :=
    { τ₁ := (t.roots v hY).hom
      τ₂ := b
      τ₃ := b
      comm₁₂ := (t.roots_normalization v hY).symm
      comm₂₃ := by
        change b ≫ (N • 𝟙 X.gmSheaf) = F.map (N • 𝟙 Y.gmSheaf) ≫ b
        rw [F.map_nsmul, F.map_id]
        simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
          Category.comp_id, Category.id_comp] }
  have hn := ShortComplex.ShortExact.extClass_naturality
    ((Y.kummerSequence_shortExact N hY).map_of_exact F)
    (X.kummerSequence_shortExact N hX) ψ
  unfold ProEtale.cartierEtaleKummerUnit ProEtale.cartierKummerClass
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_extClass]
  rw [← Ext.comp_assoc (Ext.mk₀ b) (X.kummerSequence_shortExact N hX).extClass
    (Ext.mk₀ (ordinaryFiniteRootMap A N hA X)) (zero_add 1) (add_zero 1)
    (zero_add 1)]
  rw [← hn]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rw [rootMap_pullback A N hA t v hY]

private theorem complementaryOpen_forall {D T : Scheme.{u}} (i : D ⟶ T)
    (W : T.Opens) (hW : (W : Set T) = (Set.range i.base)ᶜ) (P : T.Opens → Prop)
    (hP : P W) : ∀ (W' : T.Opens), (W' : Set T) = (Set.range i.base)ᶜ → P W' := by
  intro W' hW'
  have hw : W' = W := SetLike.coe_injective (hW'.trans hW.symm)
  simpa only [hw] using hP

private theorem boundary_equation (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤)))
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ) :
    (Ext.mk₀ (supportedIntegralGenerator A i)).comp
      (κ.mapExactFunctor (RawModuleScalarComparison.forget A T)) (zero_add 2) =
      (cartierPoleBoundary i hI).comp
        (ProEtale.cartierEtaleKummerUnit A N hA T hT) rfl := by
  let := hI.isInvertible_dual_toModules
  let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  let W : T.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  unfold SupportedKummerBoundary at hκ
  obtain ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, hext⟩ := hκ W rfl
  have hEspec : CartierPoleBoundarySpec i hI hE.extClass := by
    unfold CartierPoleBoundarySpec
    apply complementaryOpen_forall i W rfl
    exact ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, rfl⟩
  have he : hE.extClass = cartierPoleBoundary i hI :=
    (Classical.choose_spec (cartierPoleBoundary_existsUnique i hI)).2 _ hEspec
  rw [← he]
  unfold ProEtale.cartierEtaleKummerUnit ProEtale.cartierKummerClass
  simpa only [Ext.comp_assoc] using hext

/-- Cartier pullback preserves the normalized supported Kummer class, with the
canonical closed exchange and any roots-normalized twist transport.
Source: Stacks 03PL, 0A45; blueprint lemma-cycle-class-cartier-divisor, penultimate paragraph
(blueprint: lem-asd-supported-kummer-boundary-pullback).

Proof: the boundary witnesses determine the normalized integral pole class.
The integral Cartier pullback square and the Kummer short-exact-sequence square
identify the pullback of its Yoneda product with the primed product. The roots
and pure-tensor normalizations identify the coefficient-line comparison with t.
Naturality of the integral generator through closed exchange and the exact-functor
comparison identify this product with the scalar adjunct of the transported module
class. The supported integral derived unit makes this adjunct injective on Ext,
so the transported class is the supplied primed class. Cancel inverse exchange.
The argument includes N = 1 and uses no flatness of the base map. -/
theorem supported_kummer_boundary_pullback (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {D' T' : Scheme.{u}} (i' : D' ⟶ T') [IsClosedImmersion i']
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : IsPullback w i' i v)
    (hI' : i'.ker.IsInvertible)
    (κ' : Ext ((lowerStar (ModuleCat.{u + 1} A) i').obj (ordinaryFiniteConstant A D'))
      (Scheme.finiteEtaleTateLine T' N A hA) 2)
    (hκ' : SupportedKummerBoundary A N hA i' hI'
      (by simpa using hT.map v.appTop.hom) κ') :
    (Ext.mk₀ (supportedConstantExchange A i i' v w sq.toCommSq)).comp κ' (zero_add 2) =
        (κ.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) v)).comp
          (Ext.mk₀ (t.line v hT).hom) (add_zero 2) := by
  let F := upperStar (ModuleCat.{u + 1} A) v
  let G := upperStar AddCommGrpCat.{u + 1} v
  let U := moduleAbelianForget A T
  let V := moduleAbelianForget A T'
  let e := supportedConstantExchange A i i' v w sq.toCommSq
  let z := relativeExtensionExchange i i' v w sq.toCommSq
  let : IsIso e := by
    have := isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) sq
    dsimp only [e, supportedConstantExchange]
    infer_instance
  let : IsIso z := by
    have := isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} sq
    dsimp only [z, relativeExtensionExchange]
    infer_instance
  let hT' : IsUnit (N : Γ(T', ⊤)) := by simpa using hT.map v.appTop.hom
  let d := (Ext.mk₀ (asIso e).inv).comp
    ((κ.mapExactFunctor F).comp (Ext.mk₀ (t.line v hT).hom) (add_zero 2)) (zero_add 2)
  have hd : d = κ' := by
    apply (scalar_unit_ext_bijective V (supportedIntegralGenerator A i')
      (supported_integral_derived_unit T' N hN A hA i') 2).1
    have heq := scalar_adjunct_pullback F G U V (moduleAbelianUpperStarIso A v)
      (supportedIntegralGenerator A i) (supportedIntegralGenerator A i')
      (asIso z) (asIso e) (t.line v hT).hom
      (supportedGenerator_pullback A i i' v w sq.toCommSq).symm κ
    change (Ext.mk₀ (supportedIntegralGenerator A i')).comp
      (d.mapExactFunctor V) (zero_add 2) = _
    rw [heq, boundary_equation A N hA i hI hT κ hκ,
      Ext.mapExactFunctor_comp]
    rw [Ext.comp_assoc ((cartierPoleBoundary i hI).mapExactFunctor G)
      ((ProEtale.cartierEtaleKummerUnit A N hA T hT).mapExactFunctor G)
      (Ext.mk₀ ((moduleAbelianUpperStarIso A v).hom.app _ ≫
        V.map (t.line v hT).hom)) rfl (add_zero 1) (add_zero 2)]
    rw [moduleUpperStarIso_hom]
    have hk := kummerUnit_pullback A N hA t v hT hT'
    rw [← hk]
    rw [← Ext.comp_assoc _ _ _ (add_zero 1) (zero_add 1) rfl]
    rw [← cartierPoleBoundary_pullback i hI i' hI' v w sq]
    change (Ext.mk₀ (asIso z).inv).comp
      (((Ext.mk₀ z).comp (cartierPoleBoundary i' hI') (zero_add 1)).comp
        (ProEtale.cartierEtaleKummerUnit A N hA T' hT') rfl) (zero_add 2) = _
    rw [Ext.comp_assoc (Ext.mk₀ z) (cartierPoleBoundary i' hI')
      (ProEtale.cartierEtaleKummerUnit A N hA T' hT') (zero_add 1) rfl (zero_add 2)]
    simp only [Ext.mk₀_comp_mk₀_assoc, asIso_inv, IsIso.inv_hom_id,
      Ext.mk₀_id_comp]
    exact (boundary_equation A N hA i' hI' hT' κ' hκ').symm
  have hh := congrArg (fun c ↦ (Ext.mk₀ e).comp c (zero_add 2)) hd
  simpa only [d, Ext.mk₀_comp_mk₀_assoc, asIso_inv, IsIso.hom_inv_id,
    Ext.mk₀_id_comp] using hh.symm

end AlgebraicGeometry.Etale
