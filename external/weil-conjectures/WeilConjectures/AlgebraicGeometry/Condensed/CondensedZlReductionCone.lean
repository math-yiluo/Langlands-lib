/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompletedCoefficients

/-! # The normalized integral reduction cone -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem normalizedConeOfComparison
    (ℓ : ℕ) (R K : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (I : Ideal R)
    (i : ∀ X : Scheme.{u}, coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)))
    (h : SfbCompletedCoefficientComparison.{u} ℓ R K I i) :
    ∃ ρ : (Functor.const ℕᵒᵖ).obj (Mon.mk (Profinite.continuousMapRingObj.{u} R)) ⟶
        sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing,
      ∀ r, sfbConstantToContinuous R ≫ (ρ.app (op r)).hom =
        (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
          (AddCommGrpCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp
              ((Ideal.Quotient.mk (I ^ r)).comp ULift.ringEquiv.toRingHom)).toAddMonoidHom) := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, hρ.1⟩

/-- Extract just the normalized integral cone from the completed comparison.
Its components are determined by this normalization: restrict to singleton profinite
sets and use the finite constant comparison to identify arbitrary sections pointwise.
Source: completed-coefficient proposition, integral comparison and final paragraph
(blueprint: lem-pur-condensed-zl-normalized-reduction-cone).

Proof: project the integral comparison at `E = ℚ_ℓ`, retain its cone and its
normalization on constant sections, and discard the other conjuncts. -/
theorem pur_normalized_reduction_cone (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ ρ : (Functor.const ℕᵒᵖ).obj (Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[ℓ])) ⟶
        sfbCoefficientQuotientTower ℤ_[ℓ]
          (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ])) ⋙ sfbPointConstantRing,
      ∀ r, sfbConstantToContinuous ℤ_[ℓ] ≫ (ρ.app (op r)).hom =
        (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
          (AddCommGrpCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp
              ((Ideal.Quotient.mk (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]) ^ r)).comp
                ULift.ringEquiv.toRingHom)).toAddMonoidHom) := by
  exact normalizedConeOfComparison ℓ ℤ_[ℓ] ℚ_[ℓ] _ _
    (sfb_completed_coefficients.{u} ℓ).2.1

end AlgebraicGeometry.ProEtale
