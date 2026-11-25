/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerSectionCoordinates
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportUniformTorBound

/-!
# Compactly supported direct image preserves constructible towers

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
statement and proof (blueprint: prose-09-23).

The sequence-site presentation is transported along its section-normalized equivalence
with the recorded coefficient towers. All natural indices denote the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary derived equivalence induced by the section-normalized presentation.
Source: blueprint, coefficient towers and compactification composite
(blueprint: prose-09-23). -/
def spTowerShriekRealization (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) :
    spDerivedCoefficientTowers l E T D ≌ SpTowerShriek.D l E T :=
  letI := D.hasDerived
  letI := b.realizationAdditive T
  (b.realization T).mapDerivedCategory

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
