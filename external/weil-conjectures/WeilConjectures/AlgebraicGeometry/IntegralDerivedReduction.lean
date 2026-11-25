/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunction
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses

/-! # Integral derived reduction

Source: Bhatt--Scholze, Section 6.5, Definition 6.5.1 and Lemma 6.5.4;
Stacks Project, Tags 06YS and 06YY (auxiliary; not a blueprint node).

The natural-number index n denotes the positive exponent n+1. The functor is chosen
from the universal derived-change-of-rings pair, not from an arbitrary existence
statement: the universal property determines it up to unique compatible isomorphism.
-/

@[expose] public section

universe d t u

open CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (n : ℕ)

/-- Standard localization for finite quotient coefficient module sheaves.
Source: Stacks, Tag 06YY (auxiliary; not a blueprint node). -/
noncomputable instance integralReductionTargetHasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)) :=
  HasDerivedCategory.standard _

/-- The small pro-etale site fits in the ambient coefficient universe.
Source: Stacks, Tag 06YY (auxiliary; not a blueprint node). -/
noncomputable instance (priority := low) integralReductionSiteEssentiallySmall :
    EssentiallySmall.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt Y) :=
  essentiallySmallSelf _

end WeilConjectures
