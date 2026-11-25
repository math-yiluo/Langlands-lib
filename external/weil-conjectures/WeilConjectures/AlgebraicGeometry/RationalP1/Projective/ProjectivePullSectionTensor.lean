/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ProEtaleProjectionExchangeMaps
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceBaseChangeFirst
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts

/-! Tensor compatibility of the canonical pullback section, independently of Tate lines. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

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

universe u₁ u₂ u₃

@[irreducible] private def TensorComposition
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (dF : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (dG : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ E).obj G).obj G).obj (curriedTensor E))
    (dH : (Functor.postcompose₂.obj H).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ E).obj H).obj H).obj (curriedTensor E))
    (c : H ≅ F ⋙ G) : Prop :=
  ∀ A B : C, c.hom.app (A ⊗ B) ≫ G.map ((dF.app A).app B) ≫
      (dG.app (F.obj A)).app (F.obj B) =
    (dH.app A).app B ≫ tensorHom (c.hom.app A) (c.hom.app B)

namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
variable {E : Type u₃} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
  [Abelian.HasFunctorialFlatResolution E]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
  (H : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesFlat] [H.IsLeftAdjoint] [H.Monoidal]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem derived_tensor_composition (τ : H ≅ F ⋙ G)
    [NatTrans.IsMonoidal τ.hom] :
    TensorComposition F.leftDerivedFunctor G.leftDerivedFunctor H.leftDerivedFunctor
      F.leftDerivedTensorComparison G.leftDerivedTensorComparison H.leftDerivedTensorComparison
      (H.leftDerivedFunctorNatIso τ ≪≫ F.leftDerivedFunctorCompIso G) := by
  unfold TensorComposition
  exact derived_comp_explicit F G H τ
end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

section NativeTensor

attribute [-instance] internalMonoidal internalTensorCommShift

attribute [local instance 20000] traceModuleGrothendieck traceModuleFlat
  traceTensorLeft traceTensorRight traceGradedTensor traceGradedTensorLeft
  traceGradedTensorRight traceGradedTensorFour
attribute [local irreducible] CondensedRing.upperStar

private theorem tensor_hom_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    (traceTensorComparison Λ f).hom =
      (CondensedRing.upperStar Λ f).leftDerivedTensorComparison := by
  exact leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison Λ f

private def nativeIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    moduleObjectDerivedPullback Λ (𝟙 X) ≅ 𝟭 _ :=
  CondensedRing.leftDerivedUpperStarId Λ X

private def compositor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S R : Scheme.{u}}
    (f : X ⟶ S) (g : S ⟶ R) (fg : X ⟶ R) (h : f ≫ g = fg) :
    moduleObjectDerivedPullback Λ fg ≅
      moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ f :=
  eqToIso (congrArg (moduleObjectDerivedPullback Λ) h.symm) ≪≫
    modulePullbackDerivedCompositor Λ f g

private theorem compositor_tensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S R : Scheme.{u}}
    (f : X ⟶ S) (g : S ⟶ R) (fg : X ⟶ R) (h : f ≫ g = fg) :
    TensorComposition (moduleObjectDerivedPullback Λ g)
      (moduleObjectDerivedPullback Λ f) (moduleObjectDerivedPullback Λ fg)
      (traceTensorComparison Λ g).hom (traceTensorComparison Λ f).hom
      (traceTensorComparison Λ fg).hom (compositor Λ f g fg h) := by
  subst fg
  simp only [compositor, eqToIso_refl, Iso.refl_trans]
  let := upper_comp_monoidal Λ f g
  simp only [modulePullbackDerivedCompositor, tensor_hom_eq,
    CondensedRing.leftDerivedUpperStarComp_eq_leftDerivedFunctorFactorIso,
    Functor.leftDerivedFunctorFactorIso, moduleObjectDerivedPullback, tracePull]
  exact Functor.derived_tensor_composition (CondensedRing.upperStar Λ g)
    (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ (f ≫ g))
    (CondensedRing.upperStarComp Λ f g)

private theorem identity_tensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (A B : DerivedCategory (Modules Λ X)) :
    (((traceTensorComparison Λ (𝟙 X)).app A).app B).hom ≫
        tensorHom ((nativeIdentity Λ X).hom.app A)
          ((nativeIdentity Λ X).hom.app B) =
      (nativeIdentity Λ X).hom.app (A ⊗ B) := by
  exact @Adjunction.tensor_compatibility_of_unit_law _ _ _
    (moduleObjectDerivedPullback Λ (𝟙 X)) (traceTensorComparison Λ (𝟙 X)).hom
    (compositor Λ (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _))
    (nativeIdentity Λ X)
    (fun A B ↦ by
      have hc := compositor_tensor Λ (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _)
      unfold TensorComposition at hc
      exact (hc A B).symm)
    (fun A ↦ by
      have hu : (modulePullbackDerivedCompositor Λ (𝟙 X) (𝟙 X)).hom.app A ≫
          (moduleObjectDerivedPullback Λ (𝟙 X)).map ((nativeIdentity Λ X).hom.app A) =
          eqToHom (congrArg (fun k ↦ (moduleObjectDerivedPullback Λ k).obj A)
            (Category.id_comp (𝟙 X))) := by
        exact leftDerivedUpperStarComp_id_right_app Λ (𝟙 X) A
      simp only [compositor, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, Category.assoc]
      rw [hu]
      simp only [eqToHom_app, eqToHom_trans, eqToHom_refl]) A B
    (inferInstanceAs (IsIso ((((traceTensorComparison Λ (𝟙 X)).app A).app B).hom)))

private theorem eqToIso_symm_eq {C : Type*} [Category C] {A B : C} (h : A = B) :
    (eqToIso h).symm = eqToIso h.symm := by
  cases h
  rfl

/-- The native derived tensor comparison commutes with the canonical section comparison. -/
theorem pullSectionIso_tensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (A B : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPullback Λ (diagonalImmersion Y)).map
        (((traceTensorComparison Λ f).app A).app B).hom ≫
      (((traceTensorComparison Λ (diagonalImmersion Y)).app
        ((moduleObjectDerivedPullback Λ f).obj A)).app
          ((moduleObjectDerivedPullback Λ f).obj B)).hom ≫
      tensorHom ((pullSectionIso Λ Y f h).hom.app A)
        ((pullSectionIso Λ Y f h).hom.app B) =
      (pullSectionIso Λ Y f h).hom.app (A ⊗ B) := by
  let c := compositor Λ (diagonalImmersion Y) f (𝟙 (ProjectiveLine Y)) h
  have hs : c.symm ≪≫ nativeIdentity Λ (ProjectiveLine Y) =
      pullSectionIso Λ Y f h := by
    dsimp only [c, compositor]
    rw [Iso.trans_symm, eqToIso_symm_eq]
    simp only [nativeIdentity, modulePullbackDerivedCompositor,
      pullSectionIso_eq]
    exact Iso.trans_assoc _ _ _
  have hx := Adjunction.tensor_compatibility_of_composite_section
    (moduleObjectDerivedPullback Λ f)
    (moduleObjectDerivedPullback Λ (diagonalImmersion Y))
    (moduleObjectDerivedPullback Λ (𝟙 (ProjectiveLine Y)))
    (traceTensorComparison Λ f).hom (traceTensorComparison Λ (diagonalImmersion Y)).hom
    (traceTensorComparison Λ (𝟙 (ProjectiveLine Y))).hom c
    (nativeIdentity Λ (ProjectiveLine Y)) A B
    (by
      have hc := compositor_tensor Λ (diagonalImmersion Y) f (𝟙 (ProjectiveLine Y)) h
      unfold TensorComposition at hc
      exact (hc A B).symm)
    (identity_tensor Λ (ProjectiveLine Y) A B)
  rw [hs] at hx
  exact hx

end NativeTensor

end AlgebraicGeometry.ProEtale.RationalP1
