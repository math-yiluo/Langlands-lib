/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarCompletionUnitSquare
public import WeilConjectures.AlgebraicGeometry.Rational.RationalPullbackCompositionCoherence
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarOperationComp

/-! # Integral mixed geometric composition by cancellation of completion units -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
variable (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

variable (g : X ⟶ Y)
  (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
  (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
  (aE : RationalRealizationPullbackComparison l E g sXE sYE)
  (aF : RationalRealizationPullbackComparison l F g sXF sYF)

variable {Z : Scheme.{u}} [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
variable (h : Z ⟶ X) (sZE : RationalModuleRealization l E Z)
  (sZF : RationalModuleRealization l F Z)
  (ahE : RationalRealizationPullbackComparison l E h sZE sXE)
  (acE : RationalRealizationPullbackComparison l E (h ≫ g) sZE sYE)
  (ahF : RationalRealizationPullbackComparison l F h sZF sXF)
  (acF : RationalRealizationPullbackComparison l F (h ≫ g) sZF sYF)

end AlgebraicGeometry.Scheme
