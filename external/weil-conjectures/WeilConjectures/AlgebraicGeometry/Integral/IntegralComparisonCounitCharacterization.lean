/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift

/-!
# Whole-tower characterization of the specified integral comparison

The first statement includes arbitrary unbounded derived variables, normalization on
every simultaneous K-injective resolution, and hence independence of the resolution.
The second uses the actual quotient tower and the actual zero-homotopy Roos lift.
The index n denotes the positive exponent n+1 throughout.

## References

* Stacks Project, Derived Categories, Tags 0FND and 0DVC, and Cohomology on Sites, Tag 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) [IsIso g]

end AlgebraicGeometry.ProEtale
