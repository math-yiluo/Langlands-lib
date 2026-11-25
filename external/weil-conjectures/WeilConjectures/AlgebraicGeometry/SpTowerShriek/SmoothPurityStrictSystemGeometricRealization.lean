/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCoordinatesExistence
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearScalarTensorComposition
import WeilConjectures.AlgebraicGeometry.Geometry.SemilinearCoefficientPullbackComposition

/-! # A step in normalized strict compactification comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

section MatePasting
universe a v
variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type a}
  [Category.{v} A₀] [Category.{v} A₁] [Category.{v} A₂]
  [Category.{v} B₀] [Category.{v} B₁] [Category.{v} B₂]

end MatePasting

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek
