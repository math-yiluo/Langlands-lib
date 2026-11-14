import Langlands.GroupScheme.IntegralModel.InnerSemilinearExtension
import Langlands.GroupScheme.IntegralModel.FixedFieldExtension
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.GroupScheme.Descent.FiniteUnramifiedAutomorphismLift
import Langlands.Geometry.Building.UnramifiedTwistedPointStabilizer

/-! # Integral inner-twisted maps for actual unramified stabilizer models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LocalGalois.Separable
open Langlands.Geometry.Building
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IntegralModel

open GaloisPointComparison Descent.FiniteUnramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (A : MaximalUnramified.SemilinearApartmentData B)
  (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    rationalPoints (baseChanged F (inertiaFixedField F) G))
  (hc : ∀ σ τ, c (σ * τ) =
    c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))
  (y : B.ReducedBuilding) (hy : ∀ σ, A.twistedAction c hc σ y = y)
  (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (hpoints : P.integralPoints = B.oneStabilizer y)

include hy hpoints

/-- Exact identification with the full stabilizer gives forward integral-point
stability for the actual inner-twisted coefficient formula. -/
theorem twistedStabilizerModel_points_stable
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hg : g ∈ P.integralPoints) :
    c σ * rationalConjugate F (inertiaFixedField F) G σ g * (c σ)⁻¹ ∈
      P.integralPoints := by
  rw [hpoints] at hg ⊢
  have h := (A.twistedConjugation_mem_oneStabilizer_iff c hc σ g y).mpr hg
  simpa only [hy σ, twistedRationalConjugateAction_apply] using h

/-- Stabilizer transport also gives integral-point stability for the explicit
inverse of the same twisted map. -/
theorem twistedStabilizerModel_points_inverse_stable
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hg : g ∈ P.integralPoints) :
    rationalConjugate F (inertiaFixedField F) G σ.symm ((c σ)⁻¹ * g * c σ) ∈
      P.integralPoints := by
  rw [hpoints] at hg ⊢
  let g' := rationalConjugate F (inertiaFixedField F) G σ.symm ((c σ)⁻¹ * g * c σ)
  have hcancel : twistedRationalConjugateAction F G c hc σ g' = g := by
    rw [twistedRationalConjugateAction_apply]
    dsimp only [g']
    rw [rationalConjugate_symm_apply]
    simp [mul_assoc]
  have h := A.twistedConjugation_mem_oneStabilizer_iff c hc σ g' y
  rw [hy σ, hcancel] at h
  exact h.mp hg

/-- The proved strictly Henselian extension theorem gives an actual integral
isomorphism for every coefficient index on a supplied smooth stabilizer model. -/
def twistedStabilizerModelIso (hP : P.IsSmooth)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    (P.twist (fixedIntegerBaseAut F σ) (galoisBaseMap F (inertiaFixedField F) σ)
      (fixedIntegerBaseAut_generic F σ)).Iso P
        (innerGaloisDescentIso F G σ (c σ)) :=
  innerGaloisTwistIso F G P σ (c σ) (fixedIntegerBaseAut F σ)
    (fixedIntegerBaseAut_generic F σ)
    (fixedField_hasSmoothHomExtension smoothHomExtension F) hP
    (twistedStabilizerModel_points_stable A c hc y hy P hpoints σ)
    (twistedStabilizerModel_points_inverse_stable A c hc y hy P hpoints σ)

/-- The integral extension has precisely the prescribed inner-twisted generic
value on each transported integral section. -/
theorem twistedStabilizerModelIso_integralPointMap (hP : P.IsSmooth)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (x : P.integralSections) :
    P.integralPointMap
        ((twistedStabilizerModelIso A c hc y hy P hpoints hP σ).integralSectionsEquiv
          (baseChangeSectionHom (fixedIntegerBaseAut F σ) P.group x)) =
      c σ * rationalConjugate F (inertiaFixedField F) G σ (P.integralPointMap x) *
        (c σ)⁻¹ :=
  innerGaloisTwistIso_integralPointMap F G P σ (c σ) (fixedIntegerBaseAut F σ)
    (fixedIntegerBaseAut_generic F σ)
    (fixedField_hasSmoothHomExtension smoothHomExtension F) hP
    (twistedStabilizerModel_points_stable A c hc y hy P hpoints σ)
    (twistedStabilizerModel_points_inverse_stable A c hc y hy P hpoints σ) x

/-- The actual extension retains the full generic compatibility square. -/
theorem twistedStabilizerModelIso_generic_comm (hP : P.IsSmooth)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    (GroupScheme.baseChange (galoisBaseMap F (inertiaFixedField F) σ)).map
        P.genericIso.hom ≫ (innerGaloisDescentIso F G σ (c σ)).hom =
      (Descent.squareComparison (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))
        (galoisBaseMap F (inertiaFixedField F) σ) (fixedIntegerBaseAut F σ)
        (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))
        (fixedIntegerBaseAut_generic F σ) P.group).hom ≫
          (GroupScheme.baseChange
            (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).map
              (twistedStabilizerModelIso A c hc y hy P hpoints hP σ).iso.hom ≫
                P.genericIso.hom :=
  innerGaloisTwistIso_generic_comm F G P σ (c σ) (fixedIntegerBaseAut F σ)
    (fixedIntegerBaseAut_generic F σ)
    (fixedField_hasSmoothHomExtension smoothHomExtension F) hP
    (twistedStabilizerModel_points_stable A c hc y hy P hpoints σ)
    (twistedStabilizerModel_points_inverse_stable A c hc y hy P hpoints σ)

end Langlands.GroupScheme.IntegralModel
