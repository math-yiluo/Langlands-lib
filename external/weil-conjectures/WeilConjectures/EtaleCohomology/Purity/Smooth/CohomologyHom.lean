/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineKunneth

/-!
# Étale cohomology as morphisms out of the constant complex

For a scheme `X` and `K ∈ D(X_ét, Λ)`, the cohomology `H^n(X, K)` of
`AlgebraicGeometry.Etale.cohomology` is `Hom(Λ_X, K[n])`, `Λ`-linearly
(`AlgebraicGeometry.Etale.homConstantComplexLinearEquivCohomology`): the constant complex
functor is left adjoint to `RΓ(X, -)`, and `Hom(Λ[0], C) = H⁰(C)` for complexes of `Λ`-modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable (R : Type*) [Ring R] {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [HasDerivedCategory C]
  [HasDerivedCategory D] (F : C ⥤ D)
  [F.Additive] [F.Linear R] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The functor induced on derived categories by an exact `R`-linear functor is `R`-linear. -/
instance linear_mapDerivedCategory : F.mapDerivedCategory.Linear R := by
  have : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors⟩
  rw [← Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) R
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory]
  infer_instance

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- `Hom(Λ, M) ≅ M` for a `Λ`-module `M`. -/
noncomputable def ModuleCat.homSelfLinearEquiv (M : ModuleCat.{u + 1} Λ) :
    (ModuleCat.of Λ Λ ⟶ M) ≃ₗ[Λ] M where
  toFun f := f.hom (1 : Λ)
  invFun m := ModuleCat.ofHom (LinearMap.toSpanSingleton Λ M m)
  map_add' f g := rfl
  map_smul' c f := rfl
  left_inv f := by
    ext
    simp
  right_inv m := by simp

/-- An adjunction whose left adjoint is `Λ`-linear is `Λ`-linear on hom sets. -/
noncomputable def adjunctionHomLinearEquiv {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear Λ C] [Linear Λ D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [F.Additive] [F.Linear Λ] (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ₗ[Λ] (X ⟶ G.obj Y) :=
  LinearEquiv.symm
    { toEquiv := (adj.homEquiv X Y).symm
      map_add' f g := by simp [Adjunction.homEquiv_counit]
      map_smul' c f := by simp [Adjunction.homEquiv_counit] }

/-- **Étale cohomology as
morphisms**, `Hom(Λ_X, K[n]) ≅ H^n(X, K)`, `Λ`-linearly. -/
noncomputable def homConstantComplexLinearEquivCohomology (X : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    (constantComplex Λ X ⟶ K⟦n⟧) ≃ₗ[Λ] (cohomology (ModuleCat.{u + 1} Λ) X n).obj K :=
  let adj := (constantSheafΓAdj X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).mapDerivedCategoryRightDerivedAdjunction
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X
  let e₁ : (constantComplex Λ X ⟶ K⟦n⟧) ≃ₗ[Λ] ((constantFunctor Λ X).obj
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
        (ModuleCat.of Λ Λ)) ⟶ K⟦n⟧) :=
    { toEquiv := (constantFunctorObjSingleIso Λ X).homCongr (Iso.refl _) |>.symm
      map_add' f g := by simp [Iso.homCongr]
      map_smul' c f := by simp [Iso.homCongr] }
  let e₃ : ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
      (ModuleCat.of Λ Λ) ⟶ RΓ.obj (K⟦n⟧)) ≃ₗ[Λ]
      (ModuleCat.of Λ Λ ⟶ (_root_.DerivedCategory.homologyFunctor _ 0).obj (RΓ.obj (K⟦n⟧))) :=
    { toEquiv := _root_.DerivedCategory.homSingleEquivOfProjective (ModuleCat.of Λ Λ) 0 _
      map_add' f g := by
        simp [_root_.DerivedCategory.homSingleEquivOfProjective_apply,
          _root_.DerivedCategory.homSingleToHomology]
      map_smul' c f := by
        simp [_root_.DerivedCategory.homSingleEquivOfProjective_apply,
          _root_.DerivedCategory.homSingleToHomology] }
  e₁ ≪≫ₗ adjunctionHomLinearEquiv Λ adj _ _ ≪≫ₗ e₃ ≪≫ₗ
    ModuleCat.homSelfLinearEquiv Λ _ ≪≫ₗ
    ((_root_.DerivedCategory.homologyFunctor _ 0).mapIso ((RΓ.commShiftIso n).app K) ≪≫
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).shiftIso n 0 n
        (by simp)).app _).toLinearEquiv

end Etale

end AlgebraicGeometry
