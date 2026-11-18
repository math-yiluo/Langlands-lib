import Langlands.ClassFieldTheory.Local.SeparableUnramifiedInflation
import Langlands.Cohomology.Continuous.FiniteStageFactorization

/-! # Comparison with continuous inflation along fixed-field restriction -/

noncomputable section

open CategoryTheory Langlands.Continuous

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (H : OpenNormalSubgroup Gal(L/K))

local notation "E" => IntermediateField.fixedField H.toSubgroup

private def fixedFieldRestrictionHom : Gal(L/K) →ₜ* Gal(E/K) where
  __ := AlgEquiv.restrictNormalHom E
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous E

private def fixedFieldContinuousCoefficients :
    TopRep.res (fixedFieldRestrictionHom K L H) (discreteUnitsRepresentation K E) ⟶
      discreteUnitsRepresentation K L where
  hom' :=
    { toContinuousLinearMap :=
        { toLinearMap := unitInclusionLinear E L
          cont := continuous_of_discreteTopology }
      isIntertwining' σ := by
        apply ContinuousLinearMap.ext
        intro x
        apply Units.ext
        exact AlgEquiv.restrictNormal_commutes σ E x.val }

/-- Continuous inflation along restriction to the fixed field and the
inclusion of its units in the ambient field. -/
def fixedFieldContinuousUnitInflation (q : ℕ) :
    continuousCohomology q (discreteUnitsRepresentation K E) ⟶
      continuousCohomology q (discreteUnitsRepresentation K L) :=
  ContinuousCohomology.map (fixedFieldRestrictionHom K L H)
    (fixedFieldContinuousCoefficients K L H) q

set_option backward.isDefEq.respectTransparency false in
/-- Continuous inflation along actual fixed-field restriction is the finite
quotient map under the ordinary cohomology comparison. -/
theorem continuousToOrdinary_comp_fixedFieldUnitInflation (q : ℕ) :
    continuousToOrdinary (discreteUnitsRepresentation K E) q ≫
        fixedFieldUnitInflation K L H q =
      (forget₂ (TopModuleCat.{u} IntegerScalars.{u}) (ModuleCat.{u} IntegerScalars.{u})).map
        (fixedFieldContinuousUnitInflation K L H q) := by
  let : FiniteDimensional K E := fixedField_openNormal_finiteDimensional K L H
  let := continuousToOrdinary_isIso (discreteUnitsRepresentation K E) q
  let HC := FixedFieldRefinement.closed K L H
  let e := fixedFieldCohomologyIso K L HC q
  have h := finiteStageToContinuous_eq_mapIso
    (galoisUnitDiscreteModule K L) H (discreteUnitsRepresentation K E)
    (InfiniteGalois.normalAutEquivQuotient HC) (fixedFieldUnitsLinearEquiv K L H.toSubgroup)
    (fixedFieldUnitsLinearEquiv_intertwines K L HC)
    (fixedFieldRestrictionHom K L H) (fixedFieldContinuousCoefficients K L H)
    (InfiniteGalois.normalAutEquivQuotient_apply HC)
    (fun x => Units.ext (fixedFieldUnitsLinearEquiv_val K L H.toSubgroup x)) q
  unfold fixedFieldUnitInflation
  rw [h]
  change continuousToOrdinary (discreteUnitsRepresentation K E) q ≫
    e.inv ≫ e.hom ≫ inv (continuousToOrdinary (discreteUnitsRepresentation K E) q) ≫ _ = _
  rw [e.inv_hom_id_assoc, IsIso.hom_inv_id_assoc]
  rfl

/-- The two inflation constructions agree on every actual continuous class
of the finite fixed field. -/
theorem fixedFieldUnitInflation_continuousToRelative (q : ℕ)
    (x : continuousCohomology q (discreteUnitsRepresentation K E)) :
    fixedFieldUnitInflation K L H q (continuousToRelative K E q x) =
      fixedFieldContinuousUnitInflation K L H q x :=
  ConcreteCategory.congr_hom (continuousToOrdinary_comp_fixedFieldUnitInflation K L H q) x

end Langlands.ClassFieldTheory.Local
