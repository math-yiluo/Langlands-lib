import Langlands.Automorphic.GroupSchemeGrowthIndependence

/-! # Original general-linear growth spaces for any closed matrix embedding -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
local notation "std" =>
  (GroupScheme.MatrixRepresentation.standard (Fin n) (CommRingCat.of F))

local instance closedGrowthGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

omit [NumberField F] in
private theorem standard_isClosedSubgroup : GroupScheme.IsClosedSubgroup std := by
  change IsClosedImmersion (𝟙 (GLG).X.left)
  infer_instance

variable {N : ℕ}
  (rho : GroupScheme.MatrixRepresentation
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) (Fin N))
  (hrho : GroupScheme.IsClosedSubgroup rho)

include hrho

/-- The original matrix growth condition is independent of the chosen closed embedding. -/
theorem continuousGeneralLinearEquiv_mem_polynomialGrowth_of_closedImmersion
    (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈
        Langlands.Automorphic.polynomialGrowthSubrepresentation F n ↔
      f ∈ polynomialGrowthSubrepresentation F GLG rho := by
  rw [polynomialGrowthSubrepresentation_eq_of_closedImmersions F GLG rho std
    hrho (standard_isClosedSubgroup F n)]
  exact continuousGeneralLinearEquiv_mem_polynomialGrowth F n f

/-- Changing the closed embedding and then using the original matrix comparison. -/
def polynomialGrowthGeneralLinearEquivOfClosedImmersion :
    PolynomialGrowthRationalFunctions F GLG rho ≃ₗ[ℂ]
      Langlands.Automorphic.PolynomialGrowthRationalFunctions F n :=
  (polynomialGrowthChangeRepresentation F GLG rho std hrho
    (standard_isClosedSubgroup F n)).trans (polynomialGrowthGeneralLinearEquiv F n)

@[simp] theorem polynomialGrowthGeneralLinearEquivOfClosedImmersion_val
    (f : PolynomialGrowthRationalFunctions F GLG rho) :
    (polynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho f).val =
      continuousGeneralLinearEquiv F n f.val := by
  simp only [polynomialGrowthGeneralLinearEquivOfClosedImmersion, LinearEquiv.trans_apply,
    polynomialGrowthGeneralLinearEquiv_val, polynomialGrowthChangeRepresentation_val]

/-- The comparison respects the original full positive adelic right actions. -/
theorem polynomialGrowthGeneralLinearEquivOfClosedImmersion_rightAction
    (f : PolynomialGrowthRationalFunctions F GLG rho) (g : AdelicGroupPoints F GLG) :
    polynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho
        (polynomialGrowthRightAction F GLG rho g f) =
      Langlands.Automorphic.polynomialGrowthRightAction F n
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (polynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho f) := by
  apply Subtype.ext
  rw [polynomialGrowthGeneralLinearEquivOfClosedImmersion_val]
  change continuousGeneralLinearEquiv F n (continuousRightAction F GLG g f.val) =
    Langlands.Automorphic.continuousRightAction F n
      (GeneralLinearGroupPoints.adelicHomeomorph F n g)
      (polynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho f).val
  rw [polynomialGrowthGeneralLinearEquivOfClosedImmersion_val]
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

/-- Both growth realizations include into the same original ambient comparison. -/
theorem polynomialGrowthGeneralLinearEquivOfClosedImmersion_inclusion
    (f : PolynomialGrowthRationalFunctions F GLG rho) :
    Langlands.Automorphic.polynomialGrowthInclusion F n
        (polynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho f) =
      continuousGeneralLinearEquiv F n (polynomialGrowthInclusion F GLG rho f) := by
  exact polynomialGrowthGeneralLinearEquivOfClosedImmersion_val F n rho hrho f

/-- Plot-smooth slice growth agrees with the original smooth growth intersection. -/
theorem continuousGeneralLinearEquiv_mem_plotSmoothPolynomialGrowth_of_closedImmersion
    (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈
        Langlands.Automorphic.smoothPolynomialGrowthSubrepresentation F n ↔
      f ∈ plotSmoothPolynomialGrowthSubrepresentation F GLG rho := by
  rw [plotSmoothPolynomialGrowthSubrepresentation_eq_of_closedImmersions F GLG rho std
    hrho (standard_isClosedSubgroup F n)]
  exact continuousGeneralLinearEquiv_mem_plotSmoothPolynomialGrowth F n f

/-- The common finite-stabilizer condition is preserved with arbitrary closed-embedding growth. -/
theorem continuousGeneralLinearEquiv_mem_finitePlotSmoothPolynomialGrowth_of_closedImmersion
    (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈
        Langlands.Automorphic.finiteSmoothPolynomialGrowthSubrepresentation F n ↔
      f ∈ finitePlotSmoothPolynomialGrowthSubrepresentation F GLG rho := by
  rw [finitePlotSmoothPolynomialGrowthSubrepresentation_eq_of_closedImmersions F GLG rho std
    hrho (standard_isClosedSubgroup F n)]
  exact continuousGeneralLinearEquiv_mem_finitePlotSmoothPolynomialGrowth F n f

/-- Restrict the unchanged ambient map to the corresponding smooth growth subspaces. -/
def plotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion :
    ↥(plotSmoothPolynomialGrowthSubrepresentation F GLG rho).toSubmodule ≃ₗ[ℂ]
      ↥(Langlands.Automorphic.smoothPolynomialGrowthSubrepresentation F n).toSubmodule :=
  (LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (plotSmoothPolynomialGrowthSubrepresentation_eq_of_closedImmersions F GLG rho std
      hrho (standard_isClosedSubgroup F n)))).trans
    (plotSmoothPolynomialGrowthGeneralLinearEquiv F n)

/-- The stronger comparison uses the original common-stabilizer spaces. -/
def finitePlotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion :
    ↥(finitePlotSmoothPolynomialGrowthSubrepresentation F GLG rho).toSubmodule ≃ₗ[ℂ]
      ↥(Langlands.Automorphic.finiteSmoothPolynomialGrowthSubrepresentation F n).toSubmodule :=
  (LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (finitePlotSmoothPolynomialGrowthSubrepresentation_eq_of_closedImmersions F GLG rho std
      hrho (standard_isClosedSubgroup F n)))).trans
    (finitePlotSmoothPolynomialGrowthGeneralLinearEquiv F n)

@[simp] theorem plotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion_val
    (f : ↥(plotSmoothPolynomialGrowthSubrepresentation F GLG rho).toSubmodule) :
    (plotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho f).val =
      continuousGeneralLinearEquiv F n f.val := by
  change continuousGeneralLinearEquiv F n
    (LinearEquiv.ofEq _ _ _ f).val = continuousGeneralLinearEquiv F n f.val
  rw [LinearEquiv.coe_ofEq_apply]

@[simp] theorem finitePlotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion_val
    (f : ↥(finitePlotSmoothPolynomialGrowthSubrepresentation F GLG rho).toSubmodule) :
    (finitePlotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho f).val =
      continuousGeneralLinearEquiv F n f.val := by
  change continuousGeneralLinearEquiv F n
    (LinearEquiv.ofEq _ _ _ f).val = continuousGeneralLinearEquiv F n f.val
  rw [LinearEquiv.coe_ofEq_apply]

/-- Smooth growth comparison intertwines the unchanged restricted positive actions. -/
theorem plotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion_rightAction
    (f : ↥(plotSmoothPolynomialGrowthSubrepresentation F GLG rho).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    plotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho
        ((plotSmoothPolynomialGrowthSubrepresentation F GLG rho).toRepresentation g f) =
      (Langlands.Automorphic.smoothPolynomialGrowthSubrepresentation F n).toRepresentation
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (plotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho f) := by
  apply Subtype.ext
  rw [plotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion_val]
  change continuousGeneralLinearEquiv F n (continuousRightAction F GLG g f.val) =
    Langlands.Automorphic.continuousRightAction F n
      (GeneralLinearGroupPoints.adelicHomeomorph F n g)
      (plotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho f).val
  rw [plotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion_val]
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

/-- The common-stabilizer growth comparison intertwines the same full adelic actions. -/
theorem finitePlotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion_rightAction
    (f : ↥(finitePlotSmoothPolynomialGrowthSubrepresentation F GLG rho).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    finitePlotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho
        ((finitePlotSmoothPolynomialGrowthSubrepresentation F GLG rho).toRepresentation g f) =
      (Langlands.Automorphic.finiteSmoothPolynomialGrowthSubrepresentation F n).toRepresentation
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (finitePlotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho f) := by
  apply Subtype.ext
  rw [finitePlotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion_val]
  change continuousGeneralLinearEquiv F n (continuousRightAction F GLG g f.val) =
    Langlands.Automorphic.continuousRightAction F n
      (GeneralLinearGroupPoints.adelicHomeomorph F n g)
      (finitePlotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion F n rho hrho f).val
  rw [finitePlotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion_val]
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

end Langlands.Automorphic.GroupSchemeFunctions
