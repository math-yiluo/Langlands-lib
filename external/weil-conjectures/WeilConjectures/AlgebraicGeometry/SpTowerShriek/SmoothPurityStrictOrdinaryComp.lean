/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
import all WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOpenTensorCoordinates
import all WeilConjectures.AlgebraicGeometry.Geometry.SemilinearCoefficientPullbackComposition
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearNaturalIsoAssembly

/-! # Ordinary pullback compositors for strict geometric coordinates

Source: blueprint operations proof (2), constant-section inverse-image composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
attribute [local implicit_reducible] WeilConjectures.SemilinearSections.evaluation
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
attribute [local irreducible] WeilConjectures.SemilinearSections.transition
  WeilConjectures.SemilinearSections.coefficientMap
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison CategoryTheory.constantSheaf Padic
  Padic.coefficientExtensionIntegers
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek
