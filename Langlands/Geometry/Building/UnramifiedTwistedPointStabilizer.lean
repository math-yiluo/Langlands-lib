import Langlands.Geometry.Building.SemilinearCocycleStabilizer
import Langlands.Geometry.Building.UnramifiedFixedPointStabilizer
import Langlands.Geometry.Building.UnramifiedTwistedBuildingAction

/-! # Twisted conjugation on the actual unramified point stabilizer -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

section RationalPoints

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    rationalPoints (baseChanged F (inertiaFixedField F) G))
  (hc : ∀ σ τ, c (σ * τ) =
    c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))

/-- The actual inner-twisted coefficient automorphisms of `G(K)`, with `K` the
inertia fixed field of `F`. -/
def twistedRationalConjugateAction :
    (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →*
      MulAut (rationalPoints (baseChanged F (inertiaFixedField F) G)) :=
  SemilinearCocycleAction.conjugationAction
    (rationalConjugateAction F (inertiaFixedField F) G) c hc

@[simp] theorem twistedRationalConjugateAction_apply
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) :
    twistedRationalConjugateAction F G c hc σ g =
      c σ * rationalConjugate F (inertiaFixedField F) G σ g * (c σ)⁻¹ := rfl

/-- The actual character-valuation kernel is preserved and reflected by the
twisted coefficient automorphisms. No boundedness condition on `c` is needed. -/
theorem twistedRationalConjugate_mem_characterValuationKernel_iff
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) :
    twistedRationalConjugateAction F G c hc σ g ∈
        characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ↔
      g ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) :=
  SemilinearCocycleAction.conjugationAction_mem_normal_iff
    (rationalConjugateAction F (inertiaFixedField F) G) c hc
    (characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) G))
    (fun τ h => rationalConjugate_mem_characterValuationKernel_iff F
      (inertiaFixedField F) G (MaximalUnramified.valuation F) τ
      (MaximalUnramified.valuation_galois F τ) h) σ g

end RationalPoints

namespace MaximalUnramified.SemilinearApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (A : MaximalUnramified.SemilinearApartmentData B)
  (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    rationalPoints (baseChanged F (inertiaFixedField F) G))
  (hc : ∀ σ τ, c (σ * τ) =
    c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))

/-- Compatibility on the actual reduced building and rational group. -/
theorem twistedAction_smul
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (y : B.ReducedBuilding) :
    A.twistedAction c hc σ (g • y) =
      twistedRationalConjugateAction F G c hc σ g • A.twistedAction c hc σ y :=
  SemilinearCocycleAction.action_smul
    (rationalConjugateAction F (inertiaFixedField F) G) A.action A.action_smul c hc σ g y

/-- Twisted conjugation transports the actual full character-kernel stabilizer
to that of the twisted point. -/
theorem twistedConjugation_mem_oneStabilizer_iff
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (y : B.ReducedBuilding) :
    twistedRationalConjugateAction F G c hc σ g ∈
        B.oneStabilizer (A.twistedAction c hc σ y) ↔
      g ∈ B.oneStabilizer y := by
  rw [B.mem_oneStabilizer, B.mem_oneStabilizer,
    twistedRationalConjugate_mem_characterValuationKernel_iff F G c hc,
    ← A.twistedAction_smul c hc]
  exact and_congr_right fun _ => (A.twistedAction c hc σ).injective.eq_iff

/-- At a twisted-fixed point, the actual full character-kernel stabilizer carries
the inner-twisted coefficient action by group automorphisms. -/
def twistedOneStabilizerAction (y : B.ReducedBuilding)
    (hy : ∀ σ, A.twistedAction c hc σ y = y) :
    (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →* MulAut (B.oneStabilizer y) :=
  SemilinearCocycleAction.restrictGroupAction
    (twistedRationalConjugateAction F G c hc) (B.oneStabilizer y) (by
      intro σ g hg
      have h := (A.twistedConjugation_mem_oneStabilizer_iff c hc σ g y).mpr hg
      simpa only [hy σ] using h)

@[simp] theorem twistedOneStabilizerAction_apply (y : B.ReducedBuilding)
    (hy : ∀ σ, A.twistedAction c hc σ y = y)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (g : B.oneStabilizer y) :
    (A.twistedOneStabilizerAction c hc y hy σ g :
        rationalPoints (baseChanged F (inertiaFixedField F) G)) =
      c σ * rationalConjugate F (inertiaFixedField F) G σ g * (c σ)⁻¹ := rfl

end MaximalUnramified.SemilinearApartmentData

end Langlands.Geometry.Building
