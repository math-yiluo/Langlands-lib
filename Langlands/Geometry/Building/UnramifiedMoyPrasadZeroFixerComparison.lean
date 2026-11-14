import Langlands.Geometry.Building.UnramifiedNormIwahoriZeroFixer
import Langlands.Geometry.Building.IntegerValuationSharpCoverImage
import Langlands.Geometry.Building.UnramifiedZeroFixerSharpComparisonStatement

/-! # Norm-defined depth-zero groups and canonical zero point fixers -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    [IsAffineHom H.X.hom]
    (E : UnramifiedZeroDatum F H) (B : MaximalUnramified.BuildingData F H)

/-- The actual norm-defined zero-depth group is contained in the canonical
zero subgroup and fixes its point. -/
theorem moyPrasad_zero_le_zeroPoints_inf_fixer
    (hZ : IsTorus B.centralizer.Z) (x : B.Apartment) :
    B.moyPrasad hZ x 0 ≤ E.zeroPoints ⊓ B.fixer (B.apartmentMap x) := by
  have h := E.wholeApartmentZeroFixer_sup_sharpFixer_le B {x}
  rw [E.wholeApartmentZeroFixer_eq_centralizerTorusImage B hZ] at h
  change B.centralizerTorusImage hZ 0 ⊔ B.sharpFixer {x} ≤
    E.zeroPoints ⊓ B.apartment.pointwiseFixer
      (B.apartment.apartmentMap '' {x}) at h
  rw [Set.image_singleton, B.apartment.pointwiseFixer_singleton] at h
  simpa only [MaximalUnramified.BuildingData.moyPrasad_eq_sup,
    NNReal.coe_zero, B.apartment.sharpFiltration_zero] using h

/-- Regard each norm-defined depth-zero point as a canonical zero point
fixing the specified apartment point, preserving its ambient rational point. -/
def moyPrasadZeroToZeroPointFixer
    (hZ : IsTorus B.centralizer.Z) (x : B.Apartment) :
    ↥(B.moyPrasad hZ x 0) →*
      ↥(E.zeroPoints ⊓ B.fixer (B.apartmentMap x)) :=
  Subgroup.inclusion (E.moyPrasad_zero_le_zeroPoints_inf_fixer B hZ x)

/-- The existing sharp-comparison assertion identifies the canonical zero
point fixer with the actual norm-defined depth-zero group. -/
theorem zeroPoints_inf_fixer_eq_moyPrasad_of_sharpComparison
    (hSharp : UnramifiedZeroFixerSharpComparisonStatement.{u})
    (hZ : IsTorus B.centralizer.Z) (x : B.Apartment) :
    E.zeroPoints ⊓ B.fixer (B.apartmentMap x) = B.moyPrasad hZ x 0 := by
  have h := hSharp F H B E {x} (Set.singleton_nonempty x) (by
    intro f
    simpa only [Set.image_singleton] using
      (show BddAbove ({f x} : Set ℝ) from bddAbove_singleton))
  rw [E.wholeApartmentZeroFixer_eq_centralizerTorusImage B hZ] at h
  change E.zeroPoints ⊓ B.apartment.pointwiseFixer
      (B.apartment.apartmentMap '' {x}) =
    B.centralizerTorusImage hZ 0 ⊔ B.sharpFixer {x} at h
  rw [Set.image_singleton, B.apartment.pointwiseFixer_singleton] at h
  simpa only [MaximalUnramified.BuildingData.moyPrasad_eq_sup,
    NNReal.coe_zero, B.apartment.sharpFiltration_zero] using h

end Langlands.Geometry.Building.UnramifiedZeroDatum
