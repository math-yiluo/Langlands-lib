/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over

/-!
# Base change of a scheme along a field extension

For a scheme `X` over a field `k₀` and a field extension `k₀ → k₀'`, the base change
`X ×_{k₀} k₀' = X ×_{Spec k₀} Spec k₀'` is a `k₀'`-scheme through the second projection.

## Main definitions

- `AlgebraicGeometry.Scheme.baseChangeField`: the base change `X ×_{k₀} k₀'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k₀ : Type u) [Field k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  (k₀' : Type u) [Field k₀'] [Algebra k₀ k₀']

/-- The base change `X ×_{k₀} k₀'` of a `k₀`-scheme `X` along a field extension `k₀ → k₀'`, a
scheme over `k₀'` through the second projection.

(blueprint: `def-pc-base-change`) -/
noncomputable abbrev Scheme.baseChangeField : Scheme.{u} :=
  pullback (X ↘ Spec (CommRingCat.of k₀)) (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₀')))

/-- The base change `X ×_{k₀} k₀'` is a `k₀'`-scheme through the second projection. -/
noncomputable instance : (X.baseChangeField k₀ k₀').Over (Spec (CommRingCat.of k₀')) :=
  ⟨pullback.snd _ _⟩

instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    LocallyOfFiniteType (X.baseChangeField k₀ k₀' ↘ Spec (CommRingCat.of k₀')) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFiniteType)
    (IsPullback.of_hasPullback _ _) ‹_›

end AlgebraicGeometry
