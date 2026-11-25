/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# The projective line over a field is a curve

## Main statements

- `AlgebraicGeometry.topologicalKrullDim_projectiveLine_le_one`: `ℙ¹_k` has dimension at most
  one.
- `AlgebraicGeometry.isCurve_projectiveLine`: `ℙ¹_k ⟶ Spec k` is a curve.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The projective line over a field has dimension at most one: it is covered by two
affine lines, each the spectrum of a polynomial ring in one variable. -/
theorem topologicalKrullDim_projectiveLine_le_one (k : Type u) [Field k] :
    topologicalKrullDim (ProjectiveLine (Spec (.of k))) ≤ 1 := by
  refine topologicalKrullDim_le_of_iSup_eq_top _ (ProjectiveSpace.iSup_standardOpen _ _) _
    fun i ↦ ?_
  refine (IsHomeomorph.topologicalKrullDim_eq _ (ProjectiveSpace.standardOpenIso _ _ i ≪≫
    AffineSpace.SpecIso _ _).hom.homeomorph.isHomeomorph).trans_le ?_
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans_le ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

/-- The projective line over a field is a curve. -/
instance isCurve_projectiveLine (k : Type u) [Field k] :
    IsCurve (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) where
  krullDim_le_one := topologicalKrullDim_projectiveLine_le_one k

end AlgebraicGeometry
