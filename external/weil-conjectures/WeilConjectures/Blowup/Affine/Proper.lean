/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import WeilConjectures.Blowup.Affine.Defs
public import WeilConjectures.Mathlib.Algebra.DirectSum.Internal
public import WeilConjectures.Mathlib.RingTheory.ReesAlgebra

/-!

# Properness of the affine blow-up

We show that the blow-up `Bl_I (Spec A) ⟶ Spec A` of an affine scheme along a finitely
generated ideal `I : Ideal A` is proper.

Mathlib knows that `Proj 𝒜 ⟶ Spec (𝒜 0)` is proper as soon as `𝒜` is of finite type over
its degree-zero part, so the only work is to see that the Rees algebra of a finitely
generated ideal is of finite type over `reesGrading I 0 ≃+* A`. The scalar tower along
which this is transported is `SetLike.GradeZero.isScalarTower` of
`WeilConjectures.Mathlib.Algebra.DirectSum.Internal`.

## Main results

- `AlgebraicGeometry.finiteType_reesGrading_zero` — the Rees algebra of a finitely
  generated ideal is of finite type over its degree-zero part.
- `AlgebraicGeometry.AffineBlowup.isProper_toSpec` — the affine blow-up along a finitely
  generated ideal is proper.

The finite type and quasi-compactness of the same morphism are recorded alongside, since
they come from the same hypothesis.

## Blueprint

This file implements `lemma:nagata-affine-blowup-proper` of the Nagata compactification
blueprint. The blueprint derives properness from projectivity, through the closed immersion
of the blow-up into a relative projective space. We instead read it off Mathlib's
properness of `Proj.toSpecZero`, as suggested by the "Mathlib relation" paragraph of that
statement; the projective embedding is not needed for it.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The Rees algebra of a finitely generated ideal is of finite type over its degree-zero
part. This is the hypothesis of Mathlib's properness of `Proj.toSpecZero`. -/
theorem finiteType_reesGrading_zero (hI : I.FG) :
    Algebra.FiniteType (reesGrading I 0) (reesAlgebra I) :=
  have := reesAlgebra.finiteType hI
  .of_restrictScalars_finiteType A (reesGrading I 0) (reesAlgebra I)

namespace AffineBlowup

instance isIso_specMap_reesGradingZero :
    IsIso (Spec.map (CommRingCat.ofHom (reesGradingZero I).toRingHom)) :=
  have : IsIso (CommRingCat.ofHom (reesGradingZero I).toRingHom) :=
    ⟨CommRingCat.ofHom (reesGradingZero I).symm.toRingHom,
      by ext a; simp, by ext a; simp⟩
  inferInstance

section FiniteType

variable [Algebra.FiniteType (reesGrading I 0) (reesAlgebra I)]

instance locallyOfFiniteType_toSpec : LocallyOfFiniteType (toSpec I) := by
  rw [toSpec, MorphismProperty.cancel_right_of_respectsIso @LocallyOfFiniteType]
  infer_instance

instance quasiCompact_toSpec : QuasiCompact (toSpec I) := by
  rw [toSpec, MorphismProperty.cancel_right_of_respectsIso @QuasiCompact]
  infer_instance

instance isProper_toSpec_of_finiteType : IsProper (toSpec I) := by
  rw [toSpec, MorphismProperty.cancel_right_of_respectsIso @IsProper]
  infer_instance

end FiniteType

/-- **Properness of the affine blow-up**: the blow-up of `Spec A` along a finitely
generated ideal is proper over `Spec A`.
(blueprint: `lemma:nagata-affine-blowup-proper`) -/
theorem isProper_toSpec (hI : I.FG) : IsProper (toSpec I) :=
  have := finiteType_reesGrading_zero I hI
  inferInstance

/-- The affine blow-up of a Noetherian ring along any ideal is proper. -/
instance isProper_toSpec_of_isNoetherianRing [IsNoetherianRing A] : IsProper (toSpec I) :=
  isProper_toSpec I (IsNoetherian.noetherian I)

end AffineBlowup

end AlgebraicGeometry
