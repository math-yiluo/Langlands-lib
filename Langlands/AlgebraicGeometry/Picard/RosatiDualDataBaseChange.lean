import Langlands.AlgebraicGeometry.Picard.RosatiBaseChange
import Langlands.AbelianScheme.PolarizedFiniteLevel.DualWitnessBaseChange
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeMapAdditivityProof
import Langlands.AlgebraicGeometry.Picard.AffineMumfordBaseChange

/-! # Canonical base change of actual Rosati dual witnesses -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.Rosati

variable (P : Prerequisites.{u}) {S S' : Scheme.{u}} (b : S' ⟶ S)
  {A : AbelianScheme S} (W : DualData A)

/-- Transport all chosen dual witnesses using the actual Poincare comparison. -/
def DualData.baseChange : DualData ((AbelianScheme.baseChange b).obj A) where
  hasDual := hasDualScheme_baseChange P.universality b A W.hasDual
  geometry := PolarizedFiniteLevel.dualSchemeGeometry_baseChange P.universality b A
    W.hasDual W.geometry (hasDualScheme_baseChange P.universality b A W.hasDual)
  inversePoincare := PolarizedFiniteLevel.dualWitnessBaseChangeInverseBundle
    P.universality b A W.hasDual W.inversePoincare
  evaluation := PolarizedFiniteLevel.dualWitnessBaseChangeEvaluation
    P.universality b A W.hasDual W.inversePoincare P.preservation W.evaluation

/-- The packaged pullback map has precisely the canonical underlying scheme map. -/
theorem DualData.baseChangeMap_hom (lam : A ⟶ W.dual P) :
    (groupHom (DualData.baseChangeMap P b W (W.baseChange P b) lam)).hom.hom =
      dualBaseChangeMap A W.hasDual P.universality b (groupHom lam).hom.hom :=
  dualAbelianBaseChangeMap_hom P.preservation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.universality dualAbelianBaseChange b A
    W.hasDual W.geometry W.inversePoincare W.evaluation
    (W.baseChange P b).hasDual (W.baseChange P b).geometry
    (W.baseChange P b).inversePoincare (W.baseChange P b).evaluation lam

/-- An actual ample presentation transports to the canonically packaged map. -/
theorem DualData.hasAmpleMumfordPresentation_baseChange [IsAffineHom b]
    (lam : A ⟶ W.dual P)
    (h : HasAmpleMumfordPresentation P.preservation P.square A W.hasDual
      (groupHom lam).hom.hom) :
    HasAmpleMumfordPresentation P.preservation P.square ((AbelianScheme.baseChange b).obj A)
      (W.baseChange P b).hasDual
      (groupHom (DualData.baseChangeMap P b W (W.baseChange P b) lam)).hom.hom := by
  rw [DualData.baseChangeMap_hom]
  exact AbelianScheme.hasAmpleMumfordPresentation_baseChange b A P.preservation P.square
    P.universality W.hasDual _ h

variable {k : Type u} [Field k] {F : AbelianScheme (Spec (.of k))} (V : DualData F)

/-- The field additivity theorem supplies the exact Rosati additivity prerequisite. -/
theorem DualData.fieldAdditivity : V.Additivity P :=
  fieldDualSchemeMapAdditivity P.preservation P.stability k F F V.hasDual V.hasDual

end Langlands.AbelianScheme.Rosati
