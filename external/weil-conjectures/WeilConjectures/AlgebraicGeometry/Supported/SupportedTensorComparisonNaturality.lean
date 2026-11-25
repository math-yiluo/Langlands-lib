/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
public import WeilConjectures.CategoryTheory.Derived.DerivedExactMateSupplement
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientDerivedOpenMate
/-! # Naturality of normalized derived tensor comparisons

The normalization on total complexes makes the derived comparison functorial in
all three exact coefficient functors.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
section Tensor
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [HasDerivedCategory.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (G F₁ F₂ G' F₁' F₂' : C ⥤ D)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [G'.Additive] [F₁'.Additive] [F₂'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']

private def comparisonNat
    (t : supportedDerivedComparisonHom G F₁ F₂)
    (ht : ∀ M M' N N' a b,
      G.mapDerivedCategory.map (a ⊗ₘ b) ≫ t M' N' =
        t M N ≫ (F₁.mapDerivedCategory.map a ⊗ₘ F₂.mapDerivedCategory.map b)) :
    (Functor.postcompose₂.obj G.mapDerivedCategory).obj
        (curriedTensor (DerivedCategory C)) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
        F₂.mapDerivedCategory).obj (curriedTensor (DerivedCategory D)) where
  app M :=
    { app N := t M N
      naturality N N' b := by
        change G.mapDerivedCategory.map (M ◁ b) ≫ t M N' =
          t M N ≫ (F₁.mapDerivedCategory.obj M ◁ F₂.mapDerivedCategory.map b)
        simpa only [id_tensorHom, CategoryTheory.Functor.map_id] using ht M M N N' (𝟙 M) b }
  naturality M M' a := by
    ext N
    change G.mapDerivedCategory.map (a ▷ N) ≫ t M' N =
      t M N ≫ (F₁.mapDerivedCategory.map a ▷ F₂.mapDerivedCategory.obj N)
    simpa only [tensorHom_id, CategoryTheory.Functor.map_id] using ht M M' N N a (𝟙 N)

end Tensor
end AlgebraicGeometry.Etale
