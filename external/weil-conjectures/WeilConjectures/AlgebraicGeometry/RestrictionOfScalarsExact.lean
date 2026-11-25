/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunction

/-!
# Exactness of restriction from finite to completed integral coefficients

Source: Weil conjectures blueprint, `chap-Smooth-purity`, `sk-def-sf-operations`, order 1456;
Stacks Project, Tag 03DA (blueprint: lem-weil-restriction-of-scalars-exact).

The index `n : ℕ` denotes the positive exponent `n + 1`, following the coefficient
construction. Exactness of an additive functor between abelian categories is expressed
by preservation of finite limits and finite colimits.
-/

@[expose] public section

set_option autoImplicit false

universe d t u

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

/-- Restriction along the reduction from the completed coefficient sheaf to exponent
`n + 1` is exact. The target is modules over the completed ring sheaf, rather than
modules over the discrete constant valuation-ring sheaf.
Source: blueprint order 1456; Stacks Project, Tag 03DA
(blueprint: lem-weil-restriction-of-scalars-exact).

Proof:
1. On the small pro-etale site, abelian sheafification is exact
(`situation-conventions`). The coefficient construction supplies the limit
projection. Restriction along it keeps all underlying abelian sheaves and morphisms,
changing only the scalar action by precomposition with that projection; it is additive.
2. For both ring sheaves, `situation-conventions` says that
forgetting to abelian sheaves is faithful and preserves kernels and cokernels, hence
images. A short exact sequence therefore has a short exact underlying abelian sequence.
Cokernels here are sheaf cokernels, obtained by sheafifying sectionwise cokernels;
this does not assert surjectivity on sections.
3. After restriction the underlying sequence is unchanged. The kernel of its first
arrow, the cokernel of its second arrow, and its middle homology all have zero underlying
abelian sheaf by the comparisons of Step 2. Faithfulness detects zero objects, since
an identity whose image is zero is zero. Thus the restricted sequence is short exact,
which for this additive functor is equivalent to preservation of finite limits and
finite colimits. No flatness or sectionwise lifting is required. -/
theorem completedIntegralRestrictScalars_exact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (n : ℕ) :
    PreservesFiniteLimits (completedIntegralRestrictScalars l E Y D hl n) ∧
      PreservesFiniteColimits (completedIntegralRestrictScalars l E Y D hl n) := by
  let α := (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat RingCat)).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n)
  have hα : α = completedIntegralCoefficientProjection l E Y D hl n := by
    ext U x
    rfl
  change PreservesFiniteLimits (SheafOfModules.restrictScalars
      (completedIntegralCoefficientProjection l E Y D hl n)) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars
      (completedIntegralCoefficientProjection l E Y D hl n))
  rw [← hα]
  simpa [α, scalarReductionRestriction, scalarReductionSource, scalarReductionTarget] using
    (scalarReductionRestriction_exact l E Y n)

end WeilConjectures
