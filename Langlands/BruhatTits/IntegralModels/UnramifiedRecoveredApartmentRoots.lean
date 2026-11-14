import Langlands.BruhatTits.IntegralModels.UnramifiedFixedSubsetRecovery
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroRoots

/-! # Prescribed upper tori and root intersections in recovered apartment models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels
namespace RecoveredApartmentFixerModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  {D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F))}
  {Ω : Set D.Apartment}
  (M : RecoveredApartmentFixerModels D Ω)
  (hG : IsConnectedReductive G)
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)

private instance recoveredApartmentRootsExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

/-- The prescribed generic apartment torus extends to the recovered upper full
model, with its actual generic inclusion. -/
def upperFullApartmentTorus :
    IntegralSplitTorusData (S := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T)) M.upper.full
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) :=
  unramifiedIntegralSplitTorusData
    (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC)
    M.upper.full Ω M.full_integralPoints

theorem upperFullApartmentTorus_isClosedSubgroup :
    IsClosedSubgroup (M.upperFullApartmentTorus hG hiT C hDC).inclusion :=
  unramifiedIntegralSplitTorusData_isClosedSubgroup
    (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC)
    M.upper.full Ω M.full_integralPoints

/-- The same actual split torus factors through the recovered upper neutral
model, retaining the prescribed generic torus and inclusion. -/
def upperNeutralApartmentTorus :
    IntegralSplitTorusData (S := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T)) M.upper.neutral
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) :=
  (M.upperFullApartmentTorus hG hiT C hDC).factorNeutral M.upper

theorem upperNeutralApartmentTorus_isClosedSubgroup :
    IsClosedSubgroup (M.upperNeutralApartmentTorus hG hiT C hDC).inclusion :=
  (M.upperFullApartmentTorus hG hiT C hDC).factorNeutral_isClosedSubgroup
    M.upper (M.upperFullApartmentTorus_isClosedSubgroup hG hiT C hDC)

include hG hiT C hDC in
/-- The upper neutral model has the original apartment's exact root fixer
as its intersection with each actual relative root group. -/
theorem rootGroupPoints_inf_upperNeutral_eq_rootFixer
    (a : relativeRoots (T := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T))
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)) :
    rootGroupPoints (S := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T))
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) a ⊓
      M.upper.neutral.integralPoints = D.rootFixer a Ω :=
  rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer
    (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC)
    M.upper Ω M.full_integralPoints a

include hG hiT C hDC in
/-- Taking the upper neutral component preserves each actual relative-root
intersection of the recovered full model. -/
theorem rootGroupPoints_inf_upperNeutral_eq_full
    (a : relativeRoots (T := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T))
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)) :
    rootGroupPoints (S := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T))
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) a ⊓
        M.upper.neutral.integralPoints =
      rootGroupPoints (S := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T))
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) a ⊓
        M.upper.full.integralPoints := by
  let : Smooth M.upper.full.group.X.hom := M.upper.full_smooth
  exact (M.upperFullApartmentTorus hG hiT C hDC).rootGroupPoints_inf_neutral_eq_full
    M.upper a a.2.1

include hG hiT C hDC in
/-- For a nonempty affinely bounded subset, the exact upper neutral root
intersection is the original apartment filtration at its root-fixer depth. -/
theorem rootGroupPoints_inf_upperNeutral_eq_filtration
    (hne : Ω.Nonempty)
    (hb : ∀ f : D.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (a : relativeRoots (T := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T))
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (x : D.Apartment) :
    rootGroupPoints (S := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T))
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) a ⊓
      M.upper.neutral.integralPoints = D.filtration x a (D.rootFixerDepth a x Ω) :=
  rootGroupPoints_inf_unramifiedNeutral_eq_filtration
    (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC)
    M.upper Ω M.full_integralPoints hne hb a x

include hG hiT C hDC in
/-- The neutral and zero-fixer intersections agree on each original
relative-root group, for every supplied zero datum. -/
theorem rootGroupPoints_inf_upperNeutral_eq_zeroFixer
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (a : relativeRoots (T := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T))
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)) :
    rootGroupPoints (S := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T))
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) a ⊓
        M.upper.neutral.integralPoints =
      rootGroupPoints (S := ((CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T))
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) a ⊓
        (E.zeroPoints ⊓ D.pointwiseFixer (D.apartmentMap '' Ω)) :=
  rootGroupPoints_inf_unramifiedNeutral_eq_zeroFixer
    (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC)
    E M.upper Ω M.full_integralPoints a

include hG hiT C hDC in
/-- All sharp-fixer generators of the original apartment subset belong to the
recovered upper neutral model. -/
theorem sharpFixer_le_upperNeutral :
    D.sharpFixer Ω ≤ M.upper.neutral.integralPoints :=
  unramifiedSharpFixer_le_neutral
    (MaximalUnramified.buildingDataOfApartment hG hiT D C hDC)
    M.upper Ω M.full_integralPoints

end RecoveredApartmentFixerModels
end Langlands.BruhatTits.IntegralModels
