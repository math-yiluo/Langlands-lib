/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedExchangeExactNormalization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceBaseChangeFirst
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts

/-! The canonical shifted Tate comparison along a retraction of the diagonal. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

private theorem shifted_comparison_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (c : H ≅ F ⋙ G) [NatTrans.CommShift c.hom ℤ]
    (A : C) (B : D) (L : E)
    (eF : F.obj A ≅ B) (eG : G.obj B ≅ L) (eH : H.obj A ≅ L)
    (hc : c.hom.app A ≫ G.map eF.hom ≫ eG.hom = eH.hom) (n : ℤ) :
    c.hom.app ((shiftFunctor C n).obj A) ≫
        G.map ((F.commShiftIso n).hom.app A ≫ (shiftFunctor D n).map eF.hom) ≫
        (G.commShiftIso n).hom.app B ≫ (shiftFunctor E n).map eG.hom =
      (H.commShiftIso n).hom.app A ≫ (shiftFunctor E n).map eH.hom := by
  simp only [G.map_comp, Category.assoc]
  rw [G.commShiftIso_hom_naturality_assoc]
  rw [← Category.assoc (G.map ((F.commShiftIso n).hom.app A))
    ((G.commShiftIso n).hom.app (F.obj A)), ← Functor.commShiftIso_comp_hom_app]
  rw [← NatTrans.shift_app_comm_assoc]
  rw [← (shiftFunctor E n).map_comp, ← (shiftFunctor E n).map_comp, hc]

attribute [local instance 20000]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
attribute [local instance 25000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 30000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
attribute [local instance 20000] CategoryTheory.traceSheafSymmetric
attribute [local irreducible] DerivedCategory.Qh
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedTensorComparison CategoryTheory.Functor.leftDerivedFunctorCounit
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Sheaf.monObj_sheafCompose_obj
  AlgebraicGeometry.ProEtale.upperStarFromPoint

-- Expose only the canonical structure aliases when checking implicit arguments.
attribute [local implicit_reducible]
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  CategoryTheory.GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  CategoryTheory.Sheaf.symmetricCategory
  CategoryTheory.Mod.derivedMonoidalCategory

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits MonoidalCategory

@[irreducible] private def SingleComposition
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (F' : C' ⥤ D') (G' : D' ⥤ E') (H' : C' ⥤ E')
    (σC : C ⥤ C') (σD : D ⥤ D') (σE : E ⥤ E')
    (sF : σC ⋙ F' ≅ F ⋙ σD) (sG : σD ⋙ G' ≅ G ⋙ σE)
    (sH : σC ⋙ H' ≅ H ⋙ σE)
    (c : H ≅ F ⋙ G) (c' : H' ≅ F' ⋙ G') : Prop :=
  ∀ A : C, c'.hom.app (σC.obj A) ≫ G'.map (sF.hom.app A) ≫
    sG.hom.app (F.obj A) = sH.hom.app A ≫ σE.map (c.hom.app A)

namespace CategoryTheory.Functor
section GenericSectionComparisons

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

private theorem single_compositor
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (c : H ≅ F ⋙ G) :
    SingleComposition F G H F.leftDerivedFunctor G.leftDerivedFunctor H.leftDerivedFunctor
      (DerivedCategory.singleFunctor C 0) (DerivedCategory.singleFunctor D 0)
      (DerivedCategory.singleFunctor E 0)
      F.singleFunctorCompLeftDerivedFunctorIso G.singleFunctorCompLeftDerivedFunctorIso
      H.singleFunctorCompLeftDerivedFunctorIso c
      (H.leftDerivedFunctorNatIso c ≪≫ F.leftDerivedFunctorCompIso G) := by
  unfold SingleComposition
  intro A
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [leftDerivedFunctorCompIso_hom_app_singleFunctor_obj F G A]
  exact leftDerivedFunctorNatIso_hom_app_singleFunctor_obj H (F ⋙ G) c A

end GenericSectionComparisons
end CategoryTheory.Functor

private theorem single_comparison_paste
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (F' : C' ⥤ D') (G' : D' ⥤ E') (H' : C' ⥤ E')
    (σC : C ⥤ C') (σD : D ⥤ D') (σE : E ⥤ E')
    (sF : σC ⋙ F' ≅ F ⋙ σD) (sG : σD ⋙ G' ≅ G ⋙ σE)
    (sH : σC ⋙ H' ≅ H ⋙ σE)
    (c : H ≅ F ⋙ G) (c' : H' ≅ F' ⋙ G')
    (A : C) (B : D) (L : E)
    (eF : F.obj A ≅ B) (eG : G.obj B ≅ L) (eH : H.obj A ≅ L)
    (hc : c'.hom.app (σC.obj A) ≫ G'.map (sF.hom.app A) ≫
      sG.hom.app (F.obj A) = sH.hom.app A ≫ σE.map (c.hom.app A))
    (he : c.hom.app A ≫ G.map eF.hom ≫ eG.hom = eH.hom) :
    c'.hom.app (σC.obj A) ≫
      G'.map (sF.hom.app A ≫ σD.map eF.hom) ≫
      sG.hom.app B ≫ σE.map eG.hom =
    sH.hom.app A ≫ σE.map eH.hom := by
  have hn := sG.hom.naturality eF.hom
  change G'.map (σD.map eF.hom) ≫ sG.hom.app B =
    sG.hom.app (F.obj A) ≫ σE.map (G.map eF.hom) at hn
  simp only [G'.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hc, ← σE.map_comp, ← σE.map_comp, he]

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [-instance] internalMonoidal internalTensorCommShift

attribute [local instance 20000] traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour
attribute [local irreducible] CondensedRing.upperStar
attribute [local irreducible] coefficient line lineComparison shiftedLineComparison

private def nativeSingle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    DerivedCategory.singleFunctor (Modules Λ S) 0 ⋙ moduleObjectDerivedPullback Λ f ≅
      CondensedRing.upperStar Λ f ⋙ DerivedCategory.singleFunctor (Modules Λ X) 0 :=
  (CondensedRing.upperStar Λ f).singleFunctorCompLeftDerivedFunctorIso

private theorem nativeSingle_composition
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S R : Scheme.{u}}
    (f : X ⟶ S) (g : S ⟶ R) :
    SingleComposition (CondensedRing.upperStar Λ g) (CondensedRing.upperStar Λ f)
      (CondensedRing.upperStar Λ (f ≫ g))
      (moduleObjectDerivedPullback Λ g) (moduleObjectDerivedPullback Λ f)
      (moduleObjectDerivedPullback Λ (f ≫ g))
      (DerivedCategory.singleFunctor (Modules Λ R) 0)
      (DerivedCategory.singleFunctor (Modules Λ S) 0)
      (DerivedCategory.singleFunctor (Modules Λ X) 0)
      (nativeSingle Λ g) (nativeSingle Λ f) (nativeSingle Λ (f ≫ g))
      (CondensedRing.upperStarComp Λ f g) (modulePullbackDerivedCompositor Λ f g) := by
  simpa only [nativeSingle, moduleObjectDerivedPullback, modulePullbackDerivedCompositor,
    CondensedRing.leftDerivedUpperStarComp_eq_leftDerivedFunctorFactorIso,
    Functor.leftDerivedFunctorFactorIso] using
    Functor.single_compositor (CondensedRing.upperStar Λ g) (CondensedRing.upperStar Λ f)
      (CondensedRing.upperStar Λ (f ≫ g)) (CondensedRing.upperStarComp Λ f g)

private def nativeIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    moduleObjectDerivedPullback Λ (𝟙 X) ≅ 𝟭 _ :=
  CondensedRing.leftDerivedUpperStarId Λ X

private def nativeComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (A : Modules Λ S) (B : Modules Λ X) (e : (CondensedRing.upperStar Λ f).obj A ≅ B) :
    (moduleObjectDerivedPullback Λ f).obj
      ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj A) ≅
    (DerivedCategory.singleFunctor (Modules Λ X) 0).obj B :=
  (nativeSingle Λ f).app A ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e

private theorem nativeComparison_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S R : Scheme.{u}} (f : X ⟶ S) (g : S ⟶ R)
    (A : Modules Λ R) (B : Modules Λ S) (L : Modules Λ X)
    (eF : (CondensedRing.upperStar Λ g).obj A ≅ B)
    (eG : (CondensedRing.upperStar Λ f).obj B ≅ L)
    (eH : (CondensedRing.upperStar Λ (f ≫ g)).obj A ≅ L)
    (he : (CondensedRing.upperStarComp Λ f g).hom.app A ≫
      (CondensedRing.upperStar Λ f).map eF.hom ≫ eG.hom = eH.hom) :
    (modulePullbackDerivedCompositor Λ f g).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ R) 0).obj A) ≫
      (moduleObjectDerivedPullback Λ f).map (nativeComparison Λ g A B eF).hom ≫
      (nativeComparison Λ f B L eG).hom =
    (nativeComparison Λ (f ≫ g) A L eH).hom := by
  have hc := nativeSingle_composition Λ f g
  unfold SingleComposition at hc
  have hp := single_comparison_paste (CondensedRing.upperStar Λ g)
    (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ (f ≫ g))
    (moduleObjectDerivedPullback Λ g) (moduleObjectDerivedPullback Λ f)
    (moduleObjectDerivedPullback Λ (f ≫ g))
    (DerivedCategory.singleFunctor (Modules Λ R) 0)
    (DerivedCategory.singleFunctor (Modules Λ S) 0)
    (DerivedCategory.singleFunctor (Modules Λ X) 0)
    (nativeSingle Λ g) (nativeSingle Λ f) (nativeSingle Λ (f ≫ g))
    (CondensedRing.upperStarComp Λ f g) (modulePullbackDerivedCompositor Λ f g)
    A B L eF eG eH (hc A) he
  simpa only [nativeComparison, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc] using hp

private def derivedLineComparison
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (moduleObjectDerivedPullback (coefficient l c).X f).obj
        ((DerivedCategory.singleFunctor (Modules (coefficient l c).X S) 0).obj
          (line l c S)) ≅
      (DerivedCategory.singleFunctor (Modules (coefficient l c).X X) 0).obj (line l c X) :=
  (nativeSingle (coefficient l c).X f).app (line l c S) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (lineComparison l c f)

-- Elaborate the canonical derived comparison with the module instance caches folded.
private theorem derivedLineComparison_comp
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X S R : Scheme.{u}} (f : X ⟶ S) (g : S ⟶ R)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)]
    [∀ x : R, Invertible (l : R.residueField x)] :
    (modulePullbackDerivedCompositor (coefficient l c).X f g).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj (line l c R)) ≫
      (moduleObjectDerivedPullback (coefficient l c).X f).map
        (derivedLineComparison l c g).hom ≫ (derivedLineComparison l c f).hom =
      (derivedLineComparison l c (f ≫ g)).hom := by
  exact nativeComparison_comp (coefficient l c).X f g (line l c R)
    (line l c S) (line l c X) (lineComparison l c g) (lineComparison l c f)
    (lineComparison l c (f ≫ g)) (lineComparison_comp l c f g)

attribute [local instance 40000] moduleObjectDerivedPullbackCommShift

private theorem nativeCompositor_sourceShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S R : Scheme.{u}} (f : X ⟶ S) (g : S ⟶ R) :
    NatTrans.CommShift (modulePullbackDerivedCompositor Λ f g).hom ℤ := by
  dsimp only [modulePullbackDerivedCompositor]
  exact CondensedRing.pullbackComp_shift Λ f g

private theorem derivedLineComparison_hom
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (((CondensedRing.upperStar (coefficient l c).X f).singleFunctorCompLeftDerivedFunctorIso.app
      (line l c S)) ≪≫
      (DerivedCategory.singleFunctor (Modules (coefficient l c).X X) 0).mapIso
        (lineComparison l c f)).hom = (derivedLineComparison l c f).hom := by
  rfl

attribute [local irreducible] derivedLineComparison

-- Elaborate the canonical derived comparison with the module instance caches folded.
private theorem shiftedLineComparison_comp
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X S R : Scheme.{u}} (f : X ⟶ S) (g : S ⟶ R)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)]
    [∀ x : R, Invertible (l : R.residueField x)] :
    (modulePullbackDerivedCompositor (coefficient l c).X f g).hom.app
        ((shiftFunctor (DerivedCategory (Modules (coefficient l c).X R)) (2 : ℤ)).obj
          ((DerivedCategory.singleFunctor (Modules (coefficient l c).X R) 0).obj
            (line l c R))) ≫
      (moduleObjectDerivedPullback (coefficient l c).X f).map
        (shiftedLineComparison l c g).hom ≫ (shiftedLineComparison l c f).hom =
      (shiftedLineComparison l c (f ≫ g)).hom := by
  let Λ := (coefficient l c).X
  let hc : NatTrans.CommShift (modulePullbackDerivedCompositor Λ f g).hom ℤ :=
    nativeCompositor_sourceShift Λ f g
  simp only [shiftedLineComparison, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  erw [derivedLineComparison_hom l c g, derivedLineComparison_hom l c f,
    derivedLineComparison_hom l c (f ≫ g)]
  apply shifted_comparison_comp
  exact derivedLineComparison_comp l c f g

private theorem shiftedLineComparison_congr
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X S : Scheme.{u}} (f g : X ⟶ S) (h : f = g)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (shiftedLineComparison l c f).hom =
      eqToHom (congrArg (fun k ↦ (moduleObjectDerivedPullback (coefficient l c).X k).obj
        (((DerivedCategory.singleFunctor _ 0).obj (line l c S)) ⟦(2 : ℤ)⟧)) h) ≫
        (shiftedLineComparison l c g).hom := by
  subst g
  simp only [eqToHom_refl, Category.id_comp]

-- Keep the fixed coefficient and the canonical section maps folded.
/-- Pulling the fixed Tate comparison back to the diagonal gives the canonical section. -/
theorem shiftedLineComparison_section
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y)).map
        (shiftedLineComparison l c f).hom ≫
      (shiftedLineComparison l c (diagonalImmersion Y)).hom =
      (pullSectionIso (coefficient l c).X Y f h).hom.app
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X
          (ProjectiveLine Y)) 0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) := by
  let Λ := (coefficient l c).X
  let P := ProjectiveLine Y
  let B := ((DerivedCategory.singleFunctor (Modules Λ P) 0).obj (line l c P)) ⟦(2 : ℤ)⟧
  have hi : (shiftedLineComparison l c (𝟙 P)).hom =
      (nativeIdentity Λ P).hom.app B := by
    let F := moduleObjectDerivedPullback Λ (𝟙 P)
    have hf : F.Faithful := Functor.Faithful.of_iso (nativeIdentity Λ P).symm
    apply F.map_injective
    apply (cancel_epi
      ((modulePullbackDerivedCompositor Λ (𝟙 P) (𝟙 P)).hom.app B)).mp
    have hc := shiftedLineComparison_comp l c (𝟙 P) (𝟙 P)
    have hu := leftDerivedUpperStarComp_id_right_app Λ (𝟙 P) B
    rw [shiftedLineComparison_congr l c ((𝟙 P) ≫ 𝟙 P) (𝟙 P)
      (Category.id_comp _)] at hc
    have hh :
        (modulePullbackDerivedCompositor Λ (𝟙 P) (𝟙 P)).hom.app B ≫
          F.map (shiftedLineComparison l c (𝟙 P)).hom =
        eqToHom (by rw [Category.id_comp]) := by
      apply (cancel_mono (shiftedLineComparison l c (𝟙 P)).hom).mp
      simpa only [Category.assoc] using hc
    exact hh.trans hu.symm
  have hc := shiftedLineComparison_comp l c (diagonalImmersion Y) f
  rw [shiftedLineComparison_congr l c (diagonalImmersion Y ≫ f) (𝟙 P) h, hi] at hc
  apply (cancel_epi
    ((modulePullbackDerivedCompositor Λ (diagonalImmersion Y) f).hom.app B)).mp
  rw [hc]
  dsimp only [Λ, P, B] at *
  simp only [pullSectionIso_eq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    nativeIdentity, modulePullbackDerivedCompositor]
  erw [Iso.hom_inv_id_app_assoc]
  conv_rhs => erw [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  rfl

end AlgebraicGeometry.ProEtale.RationalP1
