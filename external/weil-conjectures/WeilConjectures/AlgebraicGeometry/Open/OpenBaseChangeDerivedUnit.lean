/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionFormulaCompactified
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation

/-! Normalization data for the scalar/open exchange argument. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

local notation "CR" => Scheme.proEtaleConstantRing
local notation "PB" => Scheme.proEtaleConstantRingDerivedPullback
local notation "AD" => Scheme.proEtaleRingDerivedOpenAdjunction
local notation "CC" => Scheme.proEtaleConstantRingComparison
local notation "OE" => Scheme.proEtaleRingDerivedOpenExtension

section LocalizationMate
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
  [Abelian A] [Abelian B] [Abelian D] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ D} {G₂ : D ⥤ E}
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
end LocalizationMate

variable {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₁]
  [HasDerivedCategory C₂] [HasDerivedCategory D₂]
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁) {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂}
  (adj₂ : f₂ ⊣ g₂) {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (τ : g₁ ⋙ u ≅ v ⋙ g₂) (β : u ⋙ f₂ ≅ f₁ ⋙ v)

end AlgebraicGeometry.ProEtale
