/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.InjectiveResolutionDerivedComparison
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Naturality of the explicit derived resolution comparison

Source: Stacks Project, Derived Categories, Tags 05TE and 015B.
(blueprint: lem-sc-p1-injective-resolution-derived-comparison-naturality).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
  [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]

set_option backward.isDefEq.respectTransparency false in
/-- The explicit comparison is natural for any compatible map of resolutions.

Source: Stacks Project, Derived Categories, Tags 05TE and 015B.
(blueprint: lem-sc-p1-injective-resolution-derived-comparison-naturality).

Proof: Use naturality of the chosen-resolution comparison. The two composites
from the chosen source resolution to the specified target resolution lift the
same morphism, hence are homotopic. Apply the additive functor, extend the
homotopy by zero, and localize. Naturality of mapExtendIso and of the quotient
factorization identifies the resulting equation with the asserted square. -/
theorem injectiveResolutionDerivedComparison_naturality
    (v : A ⥤ B) [v.Additive] {X Y : A} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι ≫ φ = (CochainComplex.single₀ A).map f ≫ J.ι) :
    (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        ((DerivedCategory.Plus.singleFunctor A 0).map f) ≫
      injectiveResolutionDerivedComparison v J =
    injectiveResolutionDerivedComparison v I ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((v.mapHomologicalComplex _).map φ) ComplexShape.embeddingUpNat) := by
  let ψ : (injectiveResolution X).Hom (injectiveResolution Y) f :=
    ⟨InjectiveResolution.desc f _ _, by simp⟩
  have hc := v.rightDerivedFunctorPlusObjSingleFunctorIsoQ_hom_naturality ψ
  have he : (v.mapHomologicalComplex (.up ℤ)).map ψ.hom' ≫
      ((injectiveResolution Y).cocomplex.mapExtendIso ComplexShape.embeddingUpNat v).hom =
    ((injectiveResolution X).cocomplex.mapExtendIso ComplexShape.embeddingUpNat v).hom ≫
      HomologicalComplex.extendMap ((v.mapHomologicalComplex _).map ψ.hom)
        ComplexShape.embeddingUpNat := by
    ext i
    exact HomologicalComplex.mapExtensIso_hom_f_naturality _ _ _ _
  have hh : Homotopy
      (ψ.hom ≫ InjectiveResolution.desc (𝟙 Y) J (injectiveResolution Y))
      (InjectiveResolution.desc (𝟙 X) I (injectiveResolution X) ≫ φ) := by
    apply InjectiveResolution.descHomotopy f
    · simp [ψ]
    · simp [hφ]
  have hq := DerivedCategory.Q_map_eq_of_homotopy B
    ((v.mapHomotopy hh).extend ComplexShape.embeddingUpNat)
  have hψ : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (v.rightDerivedPlusComplexMap ψ)) =
      DerivedCategory.Q.map ((v.mapHomologicalComplex (.up ℤ)).map ψ.hom') := rfl
  simp only [injectiveResolutionDerivedComparison, Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp_assoc, hc, Functor.map_comp, Category.assoc]
  rw [hψ, ← DerivedCategory.Q.map_comp_assoc]
  erw [he, Functor.map_comp, Category.assoc]
  simp only [Functor.map_comp, HomologicalComplex.extendMap_comp] at hq
  simpa only [Functor.rightDerivedFunctorPlusObjSingleFunctorIsoQ, Iso.trans_hom,
    Functor.map_comp, Category.assoc] using
    congrArg (fun g ↦ DerivedCategory.Plus.ι.map
      (v.rightDerivedFunctorPlusObjSingleFunctorIsoQ X).hom ≫
      DerivedCategory.Q.map
        ((injectiveResolution X).cocomplex.mapExtendIso ComplexShape.embeddingUpNat v).hom ≫ g)
      hq


end CategoryTheory
