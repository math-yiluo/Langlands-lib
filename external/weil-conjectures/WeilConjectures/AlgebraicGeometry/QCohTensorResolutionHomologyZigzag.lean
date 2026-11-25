/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionHomologyNaturality

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Naturality of the homology zigzag through an exact functor. -/
theorem tensorResolution_homology_zigzag
    {C : Type u} {D : Type v} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {ι : Type*} (c : ComplexShape ι) (i : ι)
    {A₀ A₁ A₂ A₃ A₄ : HomologicalComplex C c}
    {B₀ B₁ B₂ B₃ B₄ : HomologicalComplex D c}
    (a₀ : A₁ ⟶ A₀) (a₁ : A₁ ⟶ A₂) (a₂ : A₃ ⟶ A₂) (a₃ : A₃ ⟶ A₄)
    (b₀ : B₁ ⟶ B₀) (b₁ : B₁ ⟶ B₂) (b₂ : B₃ ⟶ B₂) (b₃ : B₃ ⟶ B₄)
    [QuasiIso a₀] [QuasiIso a₂] [QuasiIso b₀] [QuasiIso b₂]
    (f₀ : (F.mapHomologicalComplex c).obj A₀ ⟶ B₀)
    (f₁ : (F.mapHomologicalComplex c).obj A₁ ⟶ B₁)
    (f₂ : (F.mapHomologicalComplex c).obj A₂ ⟶ B₂)
    (f₃ : (F.mapHomologicalComplex c).obj A₃ ⟶ B₃)
    (f₄ : (F.mapHomologicalComplex c).obj A₄ ⟶ B₄)
    (h₀ : (F.mapHomologicalComplex c).map a₀ ≫ f₀ = f₁ ≫ b₀)
    (h₁ : (F.mapHomologicalComplex c).map a₁ ≫ f₂ = f₁ ≫ b₁)
    (h₂ : (F.mapHomologicalComplex c).map a₂ ≫ f₂ = f₃ ≫ b₂)
    (h₃ : (F.mapHomologicalComplex c).map a₃ ≫ f₄ = f₃ ≫ b₃) :
    F.map (inv (HomologicalComplex.homologyMap a₀ i) ≫
        HomologicalComplex.homologyMap a₁ i ≫
        inv (HomologicalComplex.homologyMap a₂ i) ≫
        HomologicalComplex.homologyMap a₃ i) ≫
        ((A₄.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap f₄ i =
      ((A₀.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap f₀ i ≫
        inv (HomologicalComplex.homologyMap b₀ i) ≫
        HomologicalComplex.homologyMap b₁ i ≫
        inv (HomologicalComplex.homologyMap b₂ i) ≫
        HomologicalComplex.homologyMap b₃ i := by
  have h := tensorResolution_zigzag_naturality
    (F.map (HomologicalComplex.homologyMap a₀ i))
    (F.map (HomologicalComplex.homologyMap a₁ i))
    (F.map (HomologicalComplex.homologyMap a₂ i))
    (F.map (HomologicalComplex.homologyMap a₃ i))
    (HomologicalComplex.homologyMap b₀ i)
    (HomologicalComplex.homologyMap b₁ i)
    (HomologicalComplex.homologyMap b₂ i)
    (HomologicalComplex.homologyMap b₃ i)
    (((A₀.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap f₀ i)
    (((A₁.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap f₁ i)
    (((A₂.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap f₂ i)
    (((A₃.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap f₃ i)
    (((A₄.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap f₄ i)
    (by simpa only [Category.assoc] using tensorResolution_homology_square F c i a₀ b₀ f₁ f₀ h₀)
    (by simpa only [Category.assoc] using tensorResolution_homology_square F c i a₁ b₁ f₁ f₂ h₁)
    (by simpa only [Category.assoc] using tensorResolution_homology_square F c i a₂ b₂ f₃ f₂ h₂)
    (by simpa only [Category.assoc] using tensorResolution_homology_square F c i a₃ b₃ f₃ f₄ h₃)
  simpa only [Functor.map_comp, Functor.map_inv, Category.assoc] using h

end AlgebraicGeometry
