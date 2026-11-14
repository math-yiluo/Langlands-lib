import Langlands.Geometry.Building.ApartmentQuotientRootDistance
import Langlands.Geometry.Building.ApartmentQuotientMovingSemilinearAction

/-! # Root-distance preservation by moving-apartment actions -/

noncomputable section

universe u uΓ

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}
  (D : KPApartmentData i ω)
  {Γ : Type uΓ} [Group Γ] {ρ : Γ →* MulAut (rationalPoints G)}
  (A : ApartmentQuotient.MovingSemilinearActionData D.sharpFixerFamily ρ)

/-- The moving action sends a translated apartment point to the translated
image of its corrected apartment coordinate. -/
theorem movingAction_smul_apartmentMap (σ : Γ) (g : rationalPoints G)
    (a : D.Apartment) :
    A.action σ (g • D.apartmentMap a) =
      (ρ σ g * A.correction σ) • D.apartmentMap (A.apartment σ a) := by
  change A.action σ (g • ApartmentQuotient.apartment D.sharpFixerFamily a) =
    (ρ σ g * A.correction σ) •
      ApartmentQuotient.apartment D.sharpFixerFamily (A.apartment σ a)
  rw [A.action_smul, A.action_apartment, mul_smul]

variable [Fintype (relativeRoots i)]

local instance : NormedAddCommGroup (TranslationSpace i) :=
  RootTranslationMetric.normedAddCommGroup i

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hcommon : D.HasCommonApartments)
  (hnorm : ∀ (σ : Γ) (a b : D.Apartment),
    ‖(A.apartment σ a -ᵥ A.apartment σ b : TranslationSpace i)‖ =
      ‖(a -ᵥ b : TranslationSpace i)‖)

include hG hi hnorm

/-- A norm-preserving moving-apartment action preserves the intrinsic chosen
distance before a metric structure has been supplied. -/
theorem chosenRootDistance_movingAction (σ : Γ) (x y : D.ReducedBuilding) :
    D.chosenRootDistance hcommon (A.action σ x) (A.action σ y) =
      D.chosenRootDistance hcommon x y := by
  obtain ⟨g, a, b, rfl, rfl⟩ := hcommon x y
  change D.chosenRootDistance hcommon (A.action σ (g • D.apartmentMap a))
    (A.action σ (g • D.apartmentMap b)) =
      D.chosenRootDistance hcommon (g • D.apartmentMap a) (g • D.apartmentMap b)
  rw [D.movingAction_smul_apartmentMap A, D.movingAction_smul_apartmentMap A,
    D.chosenRootDistance_smul_apartmentMap hG hi hcommon,
    D.chosenRootDistance_smul_apartmentMap hG hi hcommon, hnorm]

variable [PseudoMetricSpace D.ReducedBuilding]
  (hdist : ∀ x y : D.ReducedBuilding, dist x y = D.chosenRootDistance hcommon x y)

include hdist

/-- Every moving coefficient permutation is an isometry for any metric whose
distance realizes the intrinsic chosen root distance. -/
theorem movingAction_isometry (σ : Γ) :
    Isometry (α := D.ReducedBuilding) (β := D.ReducedBuilding) (A.action σ) := by
  refine Isometry.of_dist_eq fun x y => ?_
  exact (hdist (A.action σ x) (A.action σ y)).trans
    ((D.chosenRootDistance_movingAction A hG hi hcommon hnorm σ x y).trans
      (hdist x y).symm)

/-- Bundle the original moving coefficient permutation as an isometric
equivalence, retaining its exact underlying permutation. -/
def movingActionIsometryEquiv (σ : Γ) :
    D.ReducedBuilding ≃ᵢ D.ReducedBuilding where
  toEquiv := A.action σ
  isometry_toFun := D.movingAction_isometry A hG hi hcommon hnorm hdist σ

@[simp] theorem movingActionIsometryEquiv_apply (σ : Γ) (x : D.ReducedBuilding) :
    D.movingActionIsometryEquiv A hG hi hcommon hnorm hdist σ x = A.action σ x := rfl

end Langlands.Geometry.Building.KPApartmentData
