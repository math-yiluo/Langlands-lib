/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison
import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeSectionTensorForward
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalFirstPathSection

/-! # Canonical first-projection section and path comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] firstProjection
attribute [local irreducible] secondProjection square
attribute [local irreducible] projectionMap singleUnitIso
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

/-- Evaluate the native kernel prefix with an arbitrary condensed coefficient ring. -/
theorem native_section_tensor_prefix
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (source Λ Y) ⟶ N)
    (hobj : d.R₁.R.obj N =
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N)
    (hp : IsIso (projectionMap Λ (firstProjection Y) M N)) :
    ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        ((pushSectionIso Λ Y).hom.app M ≫
          (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
            ((diagonalTensorIso Λ Y M).hom ≫
              ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁
                ((supportedUnitIso Λ Y).hom ≫ α)))) ≫
      (firstPathComparison Λ Y).hom.app
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N)) ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (@inv _ _ _ _ (projectionMap Λ (firstProjection Y) M N) hp) =
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map (ρ_ M).inv ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
          d.support₁.hom ≫ d.R₁.R.map α ≫
          (eqToIso d.p₁_canonical).hom.app N ≫
          eqToHom ((congrArg (fun F => F.obj N) d.p₁_canonical).symm.trans hobj))) := by
  let w := (diagonalTensorIso Λ Y M).hom ≫
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁
      ((supportedUnitIso Λ Y).hom ≫ α))
  have hn := (firstPathComparison Λ Y).hom.naturality w
  dsimp only [Functor.comp_map] at hn
  have hs := first_path_section Λ Y M
  have hf := native_section_tensor_forward Λ Y L d M N α hobj
  let := hp
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hs]
  rw [← Functor.map_comp_assoc, hf]
  simp only [Category.assoc, ← Functor.map_comp,
    IsIso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.ProEtale.RationalP1
