import Langlands.BruhatTits.IntegralModels.UnramifiedApartmentZeroFixer
import Langlands.Geometry.Building.UnramifiedCompatibleZeroDatum

/-! # Neutral integral points from the bounded zero-fixer decomposition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (E : UnramifiedZeroDatum F G)

/-- For arbitrary original zero data, the whole-apartment zero fixer is the
Iwahori image of the constructed compatible apartment torus. -/
theorem wholeApartmentZeroFixer_eq_apartmentTorusIwahori :
    E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Set.univ) =
      (UnramifiedZeroDatum.withApartmentTorus C E).torusIwahori.map
        (rationalPoints.map (UnramifiedZeroDatum.withApartmentTorus C E).i) := by
  let E' := UnramifiedZeroDatum.withApartmentTorus C E
  have hz : E'.zeroPoints = E.zeroPoints :=
    UnramifiedZeroDatum.withApartmentTorus_zeroPoints C E
  have h := compatibleApartmentZeroFixer_eq_torusIwahori C E'
    (UnramifiedZeroDatum.withApartmentTorus_isRepresentedBy C E)
  simpa only [Set.image_univ, hz] using h

variable (Ω : Set C.Apartment)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (hN : D.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))

set_option maxHeartbeats 800000 in
include hN in
/-- The two torus inputs and the exact zero-fixer decomposition identify the
neutral integral points for every original zero datum. -/
theorem unramifiedNeutral_integralPoints_eq_zeroFixer
    (hModel : UnramifiedTorusIwahoriModelStatement.{u})
    (hBound : UnramifiedTorusConnectedBoundStatement.{u})
    (hSharp : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) =
      (E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Set.univ)) ⊔ C.sharpFixer Ω) :
    D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) := by
  have hgen := compatibleTorusIwahori_sup_sharpFixer_eq_neutral C
    (UnramifiedZeroDatum.withApartmentTorus C E)
    (UnramifiedZeroDatum.withApartmentTorus_isRepresentedBy C E)
    Ω D hN hModel hBound
  have hjoin := congrArg (fun H : Subgroup (rationalPoints G) => H ⊔ C.sharpFixer Ω)
    (wholeApartmentZeroFixer_eq_apartmentTorusIwahori C E)
  exact (hSharp.trans (hjoin.trans hgen)).symm

/-- The conditional neutral/zero-fixer identification preserves the original
ambient rational points. -/
def unramifiedNeutralZeroFixerEquiv
    (hModel : UnramifiedTorusIwahoriModelStatement.{u})
    (hBound : UnramifiedTorusConnectedBoundStatement.{u})
    (hSharp : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) =
      (E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Set.univ)) ⊔ C.sharpFixer Ω) :
    D.neutral.integralPoints ≃*
      ↥(E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) :=
  MulEquiv.subgroupCongr
    (unramifiedNeutral_integralPoints_eq_zeroFixer C E Ω D hN hModel hBound hSharp)

@[simp]
theorem coe_unramifiedNeutralZeroFixerEquiv
    (hModel : UnramifiedTorusIwahoriModelStatement.{u})
    (hBound : UnramifiedTorusConnectedBoundStatement.{u})
    (hSharp : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) =
      (E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Set.univ)) ⊔ C.sharpFixer Ω)
    (g : D.neutral.integralPoints) :
    (unramifiedNeutralZeroFixerEquiv C E Ω D hN hModel hBound hSharp g :
      rationalPoints G) = g := rfl

end Langlands.BruhatTits.IntegralModels
