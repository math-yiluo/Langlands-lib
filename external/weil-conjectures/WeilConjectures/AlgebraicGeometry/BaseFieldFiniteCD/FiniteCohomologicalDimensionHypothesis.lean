/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension

/-!
# Finite ℓ-cohomological dimension of the base field

Source: blueprint definition-cohomological-dimension and proposition-compactness-finite-coefficients
("finite type over the base field, so all cd_ℓ are finite"): the compactness input of
lemma-hypotheses-brown-representability, and so the six-functor existence results built on it,
assume cd_ℓ(k) < ∞ for the base field `k`.

`BaseFieldFiniteCD ℓ k` is the hypothesis
`cohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) < ⊤` of `brownHypotheses`, as a
definition whose body is not exposed. Statements carrying it then need only this module
publicly, not `WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension`,
whose public imports make an
unqualified `rightDerivedLowerShriekOfCompactification` inside `AlgebraicGeometry.ProEtale`
resolve to the finite-coefficient one in every importer. A file that passes it to
`brownHypotheses` imports this module with `import all`.
-/

universe u

namespace AlgebraicGeometry.ProEtale

/-- The base field `k` has finite ℓ-cohomological dimension, cd_ℓ(k) < ∞
(definition-cohomological-dimension), in the form `cohomologicalDimension ℓ _ (Spec k) < ⊤` used by
`brownHypotheses`. -/
public def BaseFieldFiniteCD (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] : Prop :=
  cohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) < ⊤

end AlgebraicGeometry.ProEtale
