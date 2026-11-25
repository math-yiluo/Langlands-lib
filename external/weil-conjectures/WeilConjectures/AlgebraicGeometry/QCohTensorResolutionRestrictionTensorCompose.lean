/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionTensor

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
open Scheme.Modules
noncomputable local instance trRestrictionTensorComposeMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Naturality of restriction tensor followed by maps on both factors. -/
theorem tensorResolutionRestrictionTensor_comp {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    {F F' G G' : Y.Modules} (f : F ⟶ F') (g : G ⟶ G')
    {H K : X.Modules}
    (a : (restrictFunctor j).obj F' ⟶ H)
    (b : (restrictFunctor j).obj G' ⟶ K) :
    (restrictFunctor j).map (f ⊗ₘ g) ≫
        (tensorResolutionRestrictionTensor j F' G').hom ≫ (a ⊗ₘ b) =
      (tensorResolutionRestrictionTensor j F G).hom ≫
        (((restrictFunctor j).map f ≫ a) ⊗ₘ
          ((restrictFunctor j).map g ≫ b)) := by
  rw [← Category.assoc, tensorResolutionRestrictionTensor_natural]
  rw [Category.assoc, tensorHom_comp_tensorHom]

/-- Compose restriction tensor naturality with two commuting factor squares. -/
theorem tensorResolutionRestrictionTensor_comp_of {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    {F F' G G' : Y.Modules} (f : F ⟶ F') (g : G ⟶ G')
    {H H' K K' : X.Modules}
    (a : (restrictFunctor j).obj F' ⟶ H')
    (b : (restrictFunctor j).obj G' ⟶ K')
    (c : (restrictFunctor j).obj F ⟶ H)
    (d : (restrictFunctor j).obj G ⟶ K)
    (f' : H ⟶ H') (g' : K ⟶ K')
    (hf : (restrictFunctor j).map f ≫ a = c ≫ f')
    (hg : (restrictFunctor j).map g ≫ b = d ≫ g') :
    (restrictFunctor j).map (f ⊗ₘ g) ≫
        (tensorResolutionRestrictionTensor j F' G').hom ≫ (a ⊗ₘ b) =
      (tensorResolutionRestrictionTensor j F G).hom ≫
        (c ⊗ₘ d) ≫ (f' ⊗ₘ g') := by
  rw [tensorResolutionRestrictionTensor_comp, hf, hg,
    ← tensorHom_comp_tensorHom]

end AlgebraicGeometry
