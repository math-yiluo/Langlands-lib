/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTowerData.FinitePullbackStrictTowerData
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerAugmentationGenerators

/-! # Augmentation square for a normalized Koszul comparison

Source: Stacks Project, sites-cohomology.tex, Tag 07A4 and sites-modules.tex, Tag 03EL.
(blueprint: lem-a1-balanced-finite-tower-augmentation-square).

The proof is the two-generator calculation on the degree minus one and degree
zero free summands, followed by sheafification and total-complex extensionality. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.FinitePullbackStrictTowerData
open WeilConjectures.CompletedPullbackUniverseTransportData
namespace WeilConjectures.BalancedFiniteTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (W : Scheme.{t})
end WeilConjectures.BalancedFiniteTower

namespace WeilConjectures.BalancedFiniteTower
open CategoryTheory.MonoidalCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (W : Scheme.{t})
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

end WeilConjectures.BalancedFiniteTower

namespace WeilConjectures.BalancedFiniteTower
open CategoryTheory.MonoidalCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)
end WeilConjectures.BalancedFiniteTower

namespace WeilConjectures.BalancedFiniteTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

end WeilConjectures.BalancedFiniteTower
