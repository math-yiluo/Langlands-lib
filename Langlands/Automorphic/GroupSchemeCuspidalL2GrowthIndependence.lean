import Langlands.Automorphic.GroupSchemeFormsGrowthIndependence
import Langlands.Automorphic.GroupSchemeRestrictionTensorCuspidalL2

/-! # Embedding independence of actual quotient cusp-form L² realizations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme Langlands.Global.PositiveRealTorus

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N M d : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (sigma : MatrixRepresentation G (Fin M))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hsigma : IsClosedSubgroup sigma)
  (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf) (hN : 0 < N) (hM : 0 < M)

/-- The original continuous cusp-form image does not depend on the closed matrix embedding. -/
theorem adelicCuspidalContinuousImage_eq_of_closedImmersions :
    adelicCuspidalContinuousImage F G Kinf rho hsmooth hcalc hPD hG hrho hK hN =
      adelicCuspidalContinuousImage F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM := by
  ext f
  change (∃ phi : AdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN,
    adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN phi = f) ↔
      ∃ phi : AdelicCuspidalForms F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM,
        adelicCuspidalToContinuous F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM phi = f
  constructor
  · rintro ⟨phi, hphi⟩
    refine ⟨adelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD phi, ?_⟩
    change (adelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD phi).val.val = f
    rw [adelicCuspidalChangeRepresentation_val]
    exact hphi
  · rintro ⟨phi, hphi⟩
    refine ⟨(adelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD).symm phi, ?_⟩
    change ((adelicCuspidalChangeRepresentation F G Kinf rho sigma hsmooth hcalc hG hrho hsigma hK hN hM hPD).symm phi).val.val = f
    rw [adelicCuspidalChangeRepresentation_symm_val]
    exact hphi

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

/-- Descent to the same actual positive quotient is unchanged. -/
theorem positiveCuspidalFormSubrepresentation_eq_of_closedImmersions :
    positiveCuspidalFormSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i =
      positiveCuspidalFormSubrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i := by
  ext f
  change (positiveQuotientContinuousPullback F G T i f ∈
    (adelicCuspidalContinuousImage F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule) ↔
      positiveQuotientContinuousPullback F G T i f ∈
        (adelicCuspidalContinuousImage F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM).toSubmodule
  rw [adelicCuspidalContinuousImage_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM]

variable (measureQ : Measure (PositiveRationalQuotient F G T i))
  (hInv : QuotientMeasureRightInvariant F G T i measureQ)

/-- The same actual square-integrability condition intersects equal descended form spaces. -/
theorem positiveCuspidalFormL2Subrepresentation_eq_of_closedImmersions :
    positiveCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv =
      positiveCuspidalFormL2Subrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv := by
  unfold positiveCuspidalFormL2Subrepresentation
  rw [positiveCuspidalFormSubrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM]

/-- Literal tensor membership is fixed on the same descended continuous functions. -/
theorem positiveTensorCuspidalFormL2Subrepresentation_eq_of_closedImmersions :
    positiveTensorCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv =
      positiveTensorCuspidalFormL2Subrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv := by
  apply Subrepresentation.toSubmodule_injective
  change (positiveCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv).toSubmodule ⊓
    (tensorPositiveQuotientSubrepresentation F G T i).toSubmodule =
      (positiveCuspidalFormL2Subrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv).toSubmodule ⊓
        (tensorPositiveQuotientSubrepresentation F G T i).toSubmodule
  rw [positiveCuspidalFormL2Subrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv]

/-- The identity equivalence on the original continuous square-integrable quotient functions. -/
def positiveCuspidalFormL2ChangeRepresentation :
    PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv ≃ₗ[ℂ]
      PositiveCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (positiveCuspidalFormL2Subrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv))

@[simp]
theorem positiveCuspidalFormL2ChangeRepresentation_val
    (f : PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv) :
    (positiveCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem positiveCuspidalFormL2ChangeRepresentation_symm_val
    (f : PositiveCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv) :
    ((positiveCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv).symm f).val = f.val :=
  LinearEquiv.coe_ofEq_apply (congrArg Subrepresentation.toSubmodule
    (positiveCuspidalFormL2Subrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv)).symm f

/-- Embedding change preserves the original positive finite right translation. -/
theorem positiveCuspidalFormL2ChangeRepresentation_finiteRightAction
    (c : FiniteAdelicGroupPoints F G) (f : PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv) :
    positiveCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv (positiveCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv c f) =
      positiveCuspidalFormL2FiniteRightAction F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv c (positiveCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f) := by
  apply Subtype.ext
  rw [positiveCuspidalFormL2ChangeRepresentation_val]
  change continuousPositiveQuotientFiniteRightAction F G T i c f.val =
    continuousPositiveQuotientFiniteRightAction F G T i c (positiveCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f).val
  rw [positiveCuspidalFormL2ChangeRepresentation_val]

/-- Both original realization maps give exactly the same actual L² class. -/
theorem positiveCuspidalFormL2ToLp_changeRepresentation
    (f : PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv) :
    positiveCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv (positiveCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f) =
      positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv f := by
  apply Lp.ext
  have h := coeFn_positiveCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv (positiveCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f)
  rw [positiveCuspidalFormL2ChangeRepresentation_val] at h
  exact h.trans (coeFn_positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv f).symm

/-- The original algebraic image in actual quotient L² is embedding independent. -/
theorem cuspidalFormQuotientL2Image_eq_of_closedImmersions :
    cuspidalFormQuotientL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv =
      cuspidalFormQuotientL2Image F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv := by
  ext phi
  change (∃ f : PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv,
    positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv f = phi) ↔
      ∃ f : PositiveCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv,
        positiveCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv f = phi
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨positiveCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f,
      positiveCuspidalFormL2ToLp_changeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f⟩
  · rintro ⟨f, rfl⟩
    refine ⟨(positiveCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv).symm f, ?_⟩
    have h := positiveCuspidalFormL2ToLp_changeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv
      ((positiveCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv).symm f)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- The identity equivalence on the original continuous square-integrable quotient functions. -/
def positiveTensorCuspidalFormL2ChangeRepresentation :
    PositiveTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv ≃ₗ[ℂ]
      PositiveTensorCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (positiveTensorCuspidalFormL2Subrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv))

@[simp]
theorem positiveTensorCuspidalFormL2ChangeRepresentation_val
    (f : PositiveTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv) :
    (positiveTensorCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem positiveTensorCuspidalFormL2ChangeRepresentation_symm_val
    (f : PositiveTensorCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv) :
    ((positiveTensorCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv).symm f).val = f.val :=
  LinearEquiv.coe_ofEq_apply (congrArg Subrepresentation.toSubmodule
    (positiveTensorCuspidalFormL2Subrepresentation_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv)).symm f

/-- Embedding change preserves the original positive finite right translation. -/
theorem positiveTensorCuspidalFormL2ChangeRepresentation_finiteRightAction
    (c : FiniteAdelicGroupPoints F G) (f : PositiveTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv) :
    positiveTensorCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv (positiveTensorCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv c f) =
      positiveTensorCuspidalFormL2FiniteRightAction F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv c (positiveTensorCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f) := by
  apply Subtype.ext
  rw [positiveTensorCuspidalFormL2ChangeRepresentation_val]
  change continuousPositiveQuotientFiniteRightAction F G T i c f.val =
    continuousPositiveQuotientFiniteRightAction F G T i c (positiveTensorCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f).val
  rw [positiveTensorCuspidalFormL2ChangeRepresentation_val]

/-- Both original realization maps give exactly the same actual L² class. -/
theorem positiveTensorCuspidalFormL2ToLp_changeRepresentation
    (f : PositiveTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv) :
    positiveTensorCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv (positiveTensorCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f) =
      positiveTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv f := by
  apply Lp.ext
  have h := coeFn_positiveTensorCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv (positiveTensorCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f)
  rw [positiveTensorCuspidalFormL2ChangeRepresentation_val] at h
  exact h.trans (coeFn_positiveTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv f).symm

/-- The original algebraic image in actual quotient L² is embedding independent. -/
theorem tensorCuspidalFormQuotientL2Image_eq_of_closedImmersions :
    tensorCuspidalFormQuotientL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv =
      tensorCuspidalFormQuotientL2Image F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv := by
  ext phi
  change (∃ f : PositiveTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv,
    positiveTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInv f = phi) ↔
      ∃ f : PositiveTensorCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv,
        positiveTensorCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM T i measureQ hInv f = phi
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨positiveTensorCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f,
      positiveTensorCuspidalFormL2ToLp_changeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv f⟩
  · rintro ⟨f, rfl⟩
    refine ⟨(positiveTensorCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv).symm f, ?_⟩
    have h := positiveTensorCuspidalFormL2ToLp_changeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv
      ((positiveTensorCuspidalFormL2ChangeRepresentation F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM T i measureQ hInv).symm f)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

end Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
  (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N M d : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (sigma : MatrixRepresentation G (Fin M))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hsigma : IsClosedSubgroup sigma)
  (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf) (hN : 0 < N) (hM : 0 < M)

/-- Descent to the same actual restriction split-centre quotient is unchanged. -/
theorem quotientCuspidalFormSubrepresentation_eq_of_closedImmersions :
    quotientCuspidalFormSubrepresentation F G S j Kinf rho hsmooth hcalc hPD hG hrho hK hN =
      quotientCuspidalFormSubrepresentation F G S j Kinf sigma hsmooth hcalc hPD hG hsigma hK hM := by
  ext f
  change (quotientContinuousPullback F G S j f ∈
    (adelicCuspidalContinuousImage F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule) ↔
      quotientContinuousPullback F G S j f ∈
        (adelicCuspidalContinuousImage F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM).toSubmodule
  rw [adelicCuspidalContinuousImage_eq_of_closedImmersions F G Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM]

variable (measureQ : Measure (Quotient F G S j))
  (hInv : QuotientRightInvariant F G measureQ)

/-- Intersect equal descended form spaces with the same actual square-integrability condition. -/
theorem quotientCuspidalFormL2Subrepresentation_eq_of_closedImmersions :
    quotientCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv =
      quotientCuspidalFormL2Subrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv := by
  unfold quotientCuspidalFormL2Subrepresentation
  rw [quotientCuspidalFormSubrepresentation_eq_of_closedImmersions F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM]

/-- The existing tensor refinement imposes the same literal tensor membership. -/
theorem quotientTensorCuspidalFormL2Subrepresentation_eq_of_closedImmersions :
    quotientTensorCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv =
      quotientTensorCuspidalFormL2Subrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv := by
  apply Subrepresentation.toSubmodule_injective
  change (quotientCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv).toSubmodule ⊓
    (quotientTensorSubrepresentation F G S j).toSubmodule =
      (quotientCuspidalFormL2Subrepresentation F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv).toSubmodule ⊓
        (quotientTensorSubrepresentation F G S j).toSubmodule
  rw [quotientCuspidalFormL2Subrepresentation_eq_of_closedImmersions F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv]

/-- The identity equivalence on the original continuous square-integrable restriction functions. -/
def quotientCuspidalFormL2ChangeRepresentation :
    QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv ≃ₗ[ℂ]
      QuotientCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (quotientCuspidalFormL2Subrepresentation_eq_of_closedImmersions F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv))

@[simp]
theorem quotientCuspidalFormL2ChangeRepresentation_val
    (f : QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv) :
    (quotientCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem quotientCuspidalFormL2ChangeRepresentation_symm_val
    (f : QuotientCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv) :
    ((quotientCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv).symm f).val = f.val :=
  LinearEquiv.coe_ofEq_apply (congrArg Subrepresentation.toSubmodule
    (quotientCuspidalFormL2Subrepresentation_eq_of_closedImmersions F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv)).symm f

/-- Embedding change preserves the original positive finite right translation. -/
theorem quotientCuspidalFormL2ChangeRepresentation_finiteRightAction
    (c : FiniteAdelicGroupPoints F G) (f : QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv) :
    quotientCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv (quotientCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv c f) =
      quotientCuspidalFormL2FiniteRightAction F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv c (quotientCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f) := by
  apply Subtype.ext
  rw [quotientCuspidalFormL2ChangeRepresentation_val]
  change continuousQuotientFiniteRightAction F G S j c f.val =
    continuousQuotientFiniteRightAction F G S j c (quotientCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f).val
  rw [quotientCuspidalFormL2ChangeRepresentation_val]

/-- Both original realization maps give exactly the same actual L² class. -/
theorem quotientCuspidalFormL2ToLp_changeRepresentation
    (f : QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv) :
    quotientCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv (quotientCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f) =
      quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv f := by
  apply Lp.ext
  have h := coeFn_quotientCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv (quotientCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f)
  rw [quotientCuspidalFormL2ChangeRepresentation_val] at h
  exact h.trans (coeFn_quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv f).symm

/-- The original algebraic image in restriction quotient L² is embedding independent. -/
theorem quotientCuspidalFormL2Image_eq_of_closedImmersions :
    quotientCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv =
      quotientCuspidalFormL2Image F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv := by
  ext phi
  change (∃ f : QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv,
    quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv f = phi) ↔
      ∃ f : QuotientCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv,
        quotientCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv f = phi
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨quotientCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f,
      quotientCuspidalFormL2ToLp_changeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f⟩
  · rintro ⟨f, rfl⟩
    refine ⟨(quotientCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv).symm f, ?_⟩
    have h := quotientCuspidalFormL2ToLp_changeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv
      ((quotientCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv).symm f)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- The identity equivalence on the original continuous square-integrable restriction functions. -/
def quotientTensorCuspidalFormL2ChangeRepresentation :
    QuotientTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv ≃ₗ[ℂ]
      QuotientTensorCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (quotientTensorCuspidalFormL2Subrepresentation_eq_of_closedImmersions F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv))

@[simp]
theorem quotientTensorCuspidalFormL2ChangeRepresentation_val
    (f : QuotientTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv) :
    (quotientTensorCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f).val = f.val :=
  LinearEquiv.coe_ofEq_apply _ f

@[simp]
theorem quotientTensorCuspidalFormL2ChangeRepresentation_symm_val
    (f : QuotientTensorCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv) :
    ((quotientTensorCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv).symm f).val = f.val :=
  LinearEquiv.coe_ofEq_apply (congrArg Subrepresentation.toSubmodule
    (quotientTensorCuspidalFormL2Subrepresentation_eq_of_closedImmersions F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv)).symm f

/-- Embedding change preserves the original positive finite right translation. -/
theorem quotientTensorCuspidalFormL2ChangeRepresentation_finiteRightAction
    (c : FiniteAdelicGroupPoints F G) (f : QuotientTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv) :
    quotientTensorCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv (quotientTensorCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv c f) =
      quotientTensorCuspidalFormL2FiniteRightAction F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv c (quotientTensorCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f) := by
  apply Subtype.ext
  rw [quotientTensorCuspidalFormL2ChangeRepresentation_val]
  change continuousQuotientFiniteRightAction F G S j c f.val =
    continuousQuotientFiniteRightAction F G S j c (quotientTensorCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f).val
  rw [quotientTensorCuspidalFormL2ChangeRepresentation_val]

/-- Both original realization maps give exactly the same actual L² class. -/
theorem quotientTensorCuspidalFormL2ToLp_changeRepresentation
    (f : QuotientTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv) :
    quotientTensorCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv (quotientTensorCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f) =
      quotientTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv f := by
  apply Lp.ext
  have h := coeFn_quotientTensorCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv (quotientTensorCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f)
  rw [quotientTensorCuspidalFormL2ChangeRepresentation_val] at h
  exact h.trans (coeFn_quotientTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv f).symm

/-- The original algebraic image in restriction quotient L² is embedding independent. -/
theorem quotientTensorCuspidalFormL2Image_eq_of_closedImmersions :
    quotientTensorCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv =
      quotientTensorCuspidalFormL2Image F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv := by
  ext phi
  change (∃ f : QuotientTensorCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv,
    quotientTensorCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN measureQ hInv f = phi) ↔
      ∃ f : QuotientTensorCuspidalFormL2Functions F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv,
        quotientTensorCuspidalFormL2ToLp F G Kinf sigma hsmooth hcalc hPD hG hsigma hK hM measureQ hInv f = phi
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨quotientTensorCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f,
      quotientTensorCuspidalFormL2ToLp_changeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv f⟩
  · rintro ⟨f, rfl⟩
    refine ⟨(quotientTensorCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv).symm f, ?_⟩
    have h := quotientTensorCuspidalFormL2ToLp_changeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv
      ((quotientTensorCuspidalFormL2ChangeRepresentation F G S j Kinf rho sigma hsmooth hcalc hPD hG hrho hsigma hK hN hM measureQ hInv).symm f)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

end Langlands.Global.RestrictionSplitCentre
