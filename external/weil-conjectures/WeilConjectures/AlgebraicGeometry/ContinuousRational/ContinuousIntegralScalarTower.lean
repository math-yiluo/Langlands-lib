/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalRealizationData
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionCoherence
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarComposition

set_option linter.privateModule false

/-! # Normalized continuous tensor coherence

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-per-continuous-integral-scalar-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (F : Type u) [Field F] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] F]

variable (G : Type u) [Field G] [Algebra ℚ_[l] G]
  [FiniteDimensional ℚ_[l] G]

end AlgebraicGeometry.Scheme.ContinuousRational
