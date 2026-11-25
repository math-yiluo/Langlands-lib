/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! Signed-total assembly of a normalized ordinary tensor comparison.

Source: Stacks, Homology, Tags 0A5J and 012Z. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.tensorObjIsoSheafification

namespace TotalAssembly
universe a b x y


section GenericTotal
variable {D : Type a} [Category.{x} D] [Preadditive D] [MonoidalCategory D]
  {E : Type b} [Category.{y} E] [Preadditive E] [MonoidalCategory E]
  [MonoidalPreadditive D] [MonoidalPreadditive E]
  [HasCoproducts.{0} D] [HasCoproducts.{0} E]
  (L : D ⥤ E) [L.Additive] [PreservesColimitsOfSize.{0, 0} L]
  (e : ∀ X Y : D, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
  (he : ∀ {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y'),
    L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))

private theorem tensorMap_factor
    {P P' Q Q' : CochainComplex D ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor D) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor D) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor D) (.up ℤ) := by
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

end GenericTotal

end TotalAssembly

end SheafOfModules.OpenTensorNormalization
