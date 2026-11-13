import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescent
import Langlands.GroupScheme.IntegralModel.UnramifiedBuildingSemilinearAction

/-! # Descent of models whose points stabilize a Galois-stable building subset -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.MaximalUnramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance extendedAffineHom :
    IsAffineHom (GroupScheme.GaloisPointComparison.baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable {C : BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (D : SemilinearApartmentData C)

/-- Coefficient conjugation preserves the setwise stabilizer of any supplied
Galois-stable subset of the original building. -/
theorem SemilinearApartmentData.conjugate_stabilizes
    {Y : Set C.ReducedBuilding}
    (hY : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, D.action σ '' Y = Y)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    {g : GroupScheme.rationalPoints (baseChanged F (inertiaFixedField F) G)}
    (hg : (g • ·) '' Y = Y) :
    (rationalConjugate F (inertiaFixedField F) G σ g • ·) '' Y = Y := by
  calc
    _ = (rationalConjugate F (inertiaFixedField F) G σ g • ·) ''
        (D.action σ '' Y) := by rw [hY σ]
    _ = D.action σ '' ((g • ·) '' Y) := by
      rw [Set.image_image, Set.image_image]
      congr 1
      funext z
      exact (D.action_smul σ g z).symm
    _ = Y := by rw [hg, hY σ]

end Langlands.Geometry.Building.MaximalUnramified

namespace Langlands.GroupScheme.IntegralModel

open Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance extendedAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable
  (hdescent : UnramifiedSmoothModelDescentStatement.{u})
  {C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (D : MaximalUnramified.SemilinearApartmentData C)
  {Y : Set C.ReducedBuilding}
  (hY : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, D.action σ '' Y = Y)
  (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (hN : N.IsSmooth)
  (hpoints : ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
    g ∈ N.integralPoints ↔ (g • ·) '' Y = Y)

include D hY hpoints in
/-- The supplied point-image comparison implies the Galois-stability premise of
smooth model descent. The subset need not be a chamber. -/
theorem stableSetModel_galois_stable
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hg : g ∈ N.integralPoints) :
    rationalConjugate F (inertiaFixedField F) G σ g ∈ N.integralPoints :=
  (hpoints _).mpr (D.conjugate_stabilizes hY σ ((hpoints g).mp hg))

include hdescent D hY hN hpoints in
/-- Conditional existence of a smooth descent with its actual generic-compatible
unramified model isomorphism. -/
theorem exists_descendedStableSetModel :
    ∃ M : IntegralModel ↥𝒪[F] F G, M.IsSmooth ∧
      Nonempty (M.baseChangeUnramified.Iso N (CategoryTheory.Iso.refl _)) :=
  hdescent F G N hN (stableSetModel_galois_stable D hY N hpoints)

/-- Choose the actual smooth model supplied by smooth model descent for the
setwise stabilizer of a supplied Galois-stable building subset. -/
def descendedStableSetModel : IntegralModel ↥𝒪[F] F G :=
  (exists_descendedStableSetModel hdescent D hY N hN hpoints).choose

theorem descendedStableSetModel_smooth :
    (descendedStableSetModel hdescent D hY N hN hpoints).IsSmooth :=
  (exists_descendedStableSetModel hdescent D hY N hN hpoints).choose_spec.1

theorem descendedStableSetModel_iso :
    Nonempty ((descendedStableSetModel hdescent D hY N hN hpoints).baseChangeUnramified.Iso
      N (CategoryTheory.Iso.refl _)) :=
  (exists_descendedStableSetModel hdescent D hY N hN hpoints).choose_spec.2

/-- The chosen descent has exactly the same original unramified integral-point
image, hence exactly the supplied setwise stabilizer. -/
theorem descendedStableSetModel_mem_integralPoints_iff
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) :
    g ∈ (descendedStableSetModel hdescent D hY N hN hpoints).baseChangeUnramified.integralPoints
      ↔ (g • ·) '' Y = Y := by
  obtain ⟨e⟩ := descendedStableSetModel_iso hdescent D hY N hN hpoints
  rw [e.integralPoints_eq]
  exact hpoints g

end Langlands.GroupScheme.IntegralModel
