/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.Algebra.DirectSum.Internal
public import WeilConjectures.RingTheory.Dehomogenization

/-!

# The standard affine chart `𝔸(n; S) ⟶ ℙ(Option n; S)`

The relative projective space `ℙ(n; S)` is defined in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, mirroring Mathlib's construction of the
relative affine space `𝔸(n; S)`: it is the base change to `S` of the integral model
`ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]`, where the polynomial ring carries its total-degree grading. Here
we construct the standard affine chart `𝔸(n; S) ⟶ ℙ(Option n; S)` onto `D₊(T₀)` by
dehomogenisation, and show that it is an open immersion over `S`.

## Main definitions

- `AlgebraicGeometry.AffineSpace.toRelativeProjectiveSpace` — the standard affine chart
  `𝔸(n; S) ⟶ ℙ(Option n; S)`, given on the integral model by `Tᵢ ↦ Tᵢ / T₀`.

## Main results

- `AlgebraicGeometry.AffineSpace.isOpenImmersion_toRelativeProjectiveSpace` — the standard
  chart is an open immersion, and it is a morphism over `S` by
  `AlgebraicGeometry.AffineSpace.toRelativeProjectiveSpace_over`.

## Implementation notes

Mathlib does not make the total-degree grading of `MvPolynomial σ R` a global instance; it is
enabled here as a local instance. The integral model
`Proj.projectiveSpaceOverAffine (Option n) (ULift ℤ)` is a plain definition rather than an
abbreviation, so that the grading instance does not leak into the statements below.

## Blueprint

This file implements `lemma:nagata-relative-affine-space-open-immersion` of the Nagata
compactification blueprint; `def:nagata-relative-projective-space` and
`lemma:nagata-projective-is-proper` are `AlgebraicGeometry.ProjectiveSpace` and
`AlgebraicGeometry.ProjectiveSpace.instIsProper`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

variable (n : Type u) (S : Scheme.{u})

local notation3 "ℤ[" n "]" => CommRingCat.of (MvPolynomial n (ULift ℤ))

local notation3 "𝒪[" n "]" => MvPolynomial.homogeneousSubmodule (Option n) (ULift ℤ)

namespace AffineSpace

/-- The standard affine chart of the integral model: the open immersion
`𝔸ⁿ_ℤ ⟶ ℙⁿ_ℤ` onto `D₊(T₀)`, given by `Tᵢ ↦ Tᵢ / T₀`. -/
noncomputable def toProjectiveSpaceInt :
    Spec ℤ[n] ⟶ Proj.projectiveSpaceOverAffine (Option n) (ULift.{u} ℤ) :=
  Spec.map (dehomogenizeEquiv n (ULift ℤ)).toCommRingCatIso.hom ≫
    Proj.awayι 𝒪[n] (X none) isHomogeneous_X_none Nat.one_pos

instance isOpenImmersion_toProjectiveSpaceInt : IsOpenImmersion (toProjectiveSpaceInt n) := by
  rw [toProjectiveSpaceInt]
  infer_instance

/-- **The standard affine chart of the relative projective space**: the open immersion
`𝔸(n; S) ⟶ ℙ(Option n; S)` over `S` identifying `𝔸(n; S)` with the standard open `D₊(T₀)`.
(blueprint: `lemma:nagata-relative-affine-space-open-immersion`) -/
noncomputable def toRelativeProjectiveSpace : 𝔸(n; S) ⟶ ℙ(Option n; S) :=
  pullback.lift (𝔸(n; S) ↘ S) (toSpecMvPoly n S ≫ toProjectiveSpaceInt n)
    (Subsingleton.elim _ _)

@[reassoc (attr := simp)]
lemma toRelativeProjectiveSpace_over :
    toRelativeProjectiveSpace n S ≫ ℙ(Option n; S) ↘ S = 𝔸(n; S) ↘ S :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma toRelativeProjectiveSpace_toProjInt :
    toRelativeProjectiveSpace n S ≫ ProjectiveSpace.toProjInt (Option n) S =
      toSpecMvPoly n S ≫ toProjectiveSpaceInt n :=
  pullback.lift_snd _ _ _

/-- The standard chart of `ℙ(Option n; S)` is the base change of the standard chart of the
integral model `ℙⁿ_ℤ`. -/
lemma isPullback_toRelativeProjectiveSpace :
    IsPullback (toSpecMvPoly n S) (toRelativeProjectiveSpace n S) (toProjectiveSpaceInt n)
      (ProjectiveSpace.toProjInt (Option n) S) := by
  refine IsPullback.of_bot ?_ (toRelativeProjectiveSpace_toProjInt n S).symm
    (ProjectiveSpace.isPullback_over_toProjInt (Option n) S).flip
  rw [toRelativeProjectiveSpace_over, Subsingleton.elim (toProjectiveSpaceInt n ≫
    terminal.from (Proj.projectiveSpaceOverAffine (Option n) (ULift.{u} ℤ)))
    (terminal.from (Spec ℤ[n]))]
  exact (IsPullback.of_hasPullback _ _).flip

instance isOpenImmersion_toRelativeProjectiveSpace :
    IsOpenImmersion (toRelativeProjectiveSpace n S) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_toRelativeProjectiveSpace n S) inferInstance

end AffineSpace

end AlgebraicGeometry
